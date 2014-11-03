import Types::*;
import ProcTypes::*;
import MemTypes::*;
import Btb::*;
import Bht::*;
import RFile::*;
import Scoreboard::*;
import FPGAMemory::*;
import Decode::*;
import Exec::*;
import Cop::*;
import Vector::*;
import Fifo::*;
import Ehr::*;

typedef struct {
    Addr pc;
    Addr nextPc;
    IType iType;
    Bool taken;
} TrainRedirect deriving (Bits, Eq);

typedef struct {
    Addr pc;
    Addr ppc;
    Bool dEp;
    Bool rEp;
    Bool eEp;
} Fetch2Decode deriving (Bits, Eq);

typedef struct {
    Addr pc;
    Addr ppc;
    DecodedInst dInst;
    Bool rEp;
    Bool eEp;
} Decode2RegRead deriving (Bits, Eq);

typedef struct {
    Addr pc;
    Addr ppc;
    DecodedInst dInst;
    Data rVal1;
    Data rVal2;
    Data copVal;
    Bool eEp;
} RegRead2Execute deriving (Bits, Eq);

typedef struct {
    IType            iType;
    Maybe#(FullIndx) dst;
    Data             data;
    Addr             addr;
} Exec2Commit deriving(Bits, Eq);

(* synthesize *)
module mkProc(Proc);
    
    Ehr#(4, Addr)  pc_reg <- mkEhr(0);
    Btb#(6,8)      btb    <- mkBtb;
    Bht#(8)        bht    <- mkBht;
    RFile          rf     <- mkRFile;
    Scoreboard#(3) sb     <- mkBypassScoreboard;
    FPGAMemory     iMem   <- mkFPGAMemory();
    FPGAMemory     dMem   <- mkFPGAMemory();
    Cop            cop    <- mkCop;
    
    Ehr#(4, Bool) dEp <- mkEhr(False);
    Ehr#(4, Bool) rEp <- mkEhr(False);
    Ehr#(4, Bool) eEp <- mkEhr(False);
    
    Fifo#(2, Fetch2Decode)    decodeFifo    <- mkCFFifo;
    Fifo#(2, Decode2RegRead)  regReadFifo   <- mkCFFifo;
    Fifo#(2, RegRead2Execute) executeFifo   <- mkCFFifo;
    Fifo#(2, Exec2Commit)     memoryFifo    <- mkCFFifo;
    Fifo#(2, Exec2Commit)     writeBackFifo <- mkCFFifo;
    
    Bool memReady = iMem.init.done() && dMem.init.done();
    
    rule doFetch( cop.started && memReady && decodeFifo.notFull );
        
        // Fetch Instruction
        let pc  = pc_reg[3];
        let ppc = btb.predPc(pc);
        iMem.req( MemReq{ op: Ld, addr: pc, data: ? } );
        
        // Update PC
        pc_reg[3] <= ppc;
        
        // Create and push Fetch2Decode
        Fetch2Decode d;
	d.pc  = pc;
	d.ppc = ppc;
        d.dEp = dEp[3];
        d.rEp = rEp[3];
        d.eEp = eEp[3];
        decodeFifo.enq(d);

    endrule
    
    rule doDecode( cop.started && memReady && decodeFifo.notEmpty && regReadFifo.notFull );
        
        // Retrieve Fetch2Decode & Instruction
        let d = decodeFifo.first; decodeFifo.deq;
        let inst <- iMem.resp;
        
        if( d.eEp == eEp[2] && d.rEp == rEp[2] && d.dEp == dEp[2] ) begin
            
            // Decode Instruction
            let dInst = decode(inst);
            
            // Predict Branch
            let nextPc  = d.pc + 4;
            let taken   = bht.predict(d.pc);
            if( dInst.iType == J ) nextPc[27:0] = validValue(dInst.imm)[27:0];
            else if( dInst.iType == Br ) begin if( taken ) nextPc = nextPc + validValue(dInst.imm); end
            else nextPc = d.ppc;
            
            // Create and push Decode2RegRead
            Decode2RegRead rr;
            rr.pc    = d.pc;
            rr.ppc   = nextPc;
            rr.dInst = dInst;
            rr.rEp   = d.rEp;
            rr.eEp   = d.eEp;
            regReadFifo.enq(rr);
            
            // Handle misprediction
            if( d.ppc != nextPc ) begin
                pc_reg[2] <= nextPc;
                dEp[2]    <= !dEp[2];
            end
            
        end
        
    endrule
    
    rule doRegRead( cop.started && memReady && regReadFifo.notEmpty && executeFifo.notFull );
        
        // Retrieve Decode2RegRead
        let rr = regReadFifo.first;
        
        if( rr.eEp != eEp[1] || rr.rEp != rEp[1] ) regReadFifo.deq;
        else begin
            
            // Ensure no dependencies
            Bool stall = sb.search1( rr.dInst.src1 ) || sb.search2( rr.dInst.src2 );
	    if( !stall ) begin
                
                regReadFifo.deq;
                
                // Create and push RegRead2Execute
                RegRead2Execute e;
                e.pc     = rr.pc;
                e.dInst  = rr.dInst;
                e.rVal1  = rf.rd1( validRegValue( rr.dInst.src1 ) );
                e.rVal2  = rf.rd2( validRegValue( rr.dInst.src2 ) );
                e.copVal = cop.rd( validRegValue( rr.dInst.src1 ) );
                e.ppc    = rr.dInst.iType == Jr ? e.rVal1 : rr.ppc;
                e.eEp    = rr.eEp;
                executeFifo.enq(e);
                
                // Update scoreboard
                sb.insert( rr.dInst.dst );
                
                // Handle misprediction
                if( rr.ppc != e.ppc ) begin
                    pc_reg[1] <= e.ppc;
                    rEp[1]    <= !rEp[1];
                end
                
	    end
            
        end
        
    endrule
    
    rule doExecute( cop.started && memReady && executeFifo.notEmpty && memoryFifo.notFull );
        
        // Retrieve RegRead2Execute
        let e = executeFifo.first; executeFifo.deq;
        
        if( e.eEp != eEp[0] ) begin
            memoryFifo.enq( Exec2Commit{ iType: Unsupported, dst: Invalid, data: ?, addr: ? } );
        end else begin
            
            // Execute
            let eInst = exec( e.dInst, e.rVal1, e.rVal2, e.pc, e.ppc, e.copVal );
            if(eInst.iType == Unsupported) begin
                $fwrite( stderr, "Executing unsupported instruction at pc: %x. Exiting\n", e.pc );
                $finish;
            end
            
            // Handle misprediction
            if( eInst.mispredict ) begin
                pc_reg[0] <= eInst.addr;
                eEp[0]    <= !eEp[0];
            end
            
            // Train BTB & BHT
            if( eInst.iType == J  || eInst.iType == Jr || eInst.iType == Br ) begin
                btb.update( e.pc, eInst.addr );
            end
            if( eInst.iType == Br ) bht.train( e.pc, eInst.brTaken );
            
            // Push Exec2Commit
            Exec2Commit c;
            c.iType = eInst.iType;
            c.dst   = eInst.dst;
            c.data  = eInst.data;
            c.addr  = eInst.addr;
            memoryFifo.enq(c);
            
        end
        
    endrule
    
    rule doMemory( cop.started && memReady && memoryFifo.notEmpty && writeBackFifo.notFull );
        
        // Retrieve Exec2Commit
        let c = memoryFifo.first; memoryFifo.deq;
        
        // Memory
        if( c.iType == Ld ) dMem.req( MemReq{ op: Ld, addr: c.addr, data: c.data } );
        if( c.iType == St ) dMem.req( MemReq{ op: St, addr: c.addr, data: c.data } );
        
        // Push Exec2Commit
        writeBackFifo.enq(c);
    
    endrule
    
    rule doWriteBack( cop.started && memReady && writeBackFifo.notEmpty );
        
        // Retrieve Exec2Commit
        let c = writeBackFifo.first; writeBackFifo.deq;
        
        // Update c.data with memory data if applicable
        if( c.iType == Ld ) c.data <- dMem.resp;
            
        // Write Back
        if( isValid( c.dst ) && validValue( c.dst ).regType == Normal ) begin
            rf.wr( validRegValue(c.dst), c.data );
        end
        cop.wr( c.dst, c.data );
        sb.remove;
        
    endrule
    
    method ActionValue#(Tuple2#(RIndx, Data)) cpuToHost;
        let ret <- cop.cpuToHost;
        return ret;
    endmethod
    
    method Action hostToCpu(Bit#(32) startpc) if ( !cop.started && memReady );
        cop.start;
        pc_reg[3] <= startpc;
    endmethod
    
    interface MemInit iMemInit = iMem.init;
    interface MemInit dMemInit = dMem.init;
    
endmodule

