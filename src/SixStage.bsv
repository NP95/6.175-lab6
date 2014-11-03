import Types::*;
import ProcTypes::*;
import MemTypes::*;
import Btb::*;
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
    Addr ppc;
    Bool epoch;
} Fetch2Decode deriving (Bits, Eq);

typedef struct {
    Addr pc;
    Addr ppc;
    DecodedInst dInst;
    Bool epoch;
} Decode2RegRead deriving (Bits, Eq);

typedef struct {
    Addr pc;
    Addr ppc;
    DecodedInst dInst;
    Data rVal1;
    Data rVal2;
    Data copVal;
    Bool epoch;
} RegRead2Execute deriving (Bits, Eq);

typedef struct {
    IType            iType;
    Maybe#(FullIndx) dst;
    Data             data;
    Addr             addr;
} Exec2Commit deriving(Bits, Eq);

(* synthesize *)
module mkProc(Proc);
    
    Reg#(Addr)     pc_reg <- mkRegU;
    Btb#(6,8)      btb    <- mkBtb;
    RFile          rf     <- mkRFile;
    Scoreboard#(3) sb     <- mkBypassScoreboard;
    FPGAMemory     iMem   <- mkFPGAMemory();
    FPGAMemory     dMem   <- mkFPGAMemory();
    Cop            cop    <- mkCop;
    
    Reg#(Bool) fEpoch <- mkReg(False);
    Reg#(Bool) eEpoch <- mkReg(False);
    
    Bool memReady = iMem.init.done() && dMem.init.done();
    
    Fifo#(2, Redirect)        redirectFifo  <- mkBypassFifo;
    Fifo#(2, Fetch2Decode)    decodeFifo    <- mkCFFifo;
    Fifo#(2, Decode2RegRead)  regReadFifo   <- mkCFFifo;
    Fifo#(2, RegRead2Execute) executeFifo   <- mkCFFifo;
    Fifo#(2, Exec2Commit)     memoryFifo    <- mkCFFifo;
    Fifo#(2, Exec2Commit)     writeBackFifo <- mkCFFifo;
    
    rule doFetch( cop.started && memReady && decodeFifo.notFull );
        if( redirectFifo.notEmpty ) begin
            
            // Retrieve redirect information
            let r = redirectFifo.first; redirectFifo.deq;
            
            // Train BTB
            btb.update( r.pc, r.nextPc );
            
            // Correct misprediction
            pc_reg <= r.nextPc;
            fEpoch <= !fEpoch;
            
        end else begin
            
            // Fetch Instruction
            let pc  = pc_reg;
            let ppc = btb.predPc(pc);
            iMem.req( MemReq{ op: Ld, addr: pc, data: ? } );
            
            // Update PC
            pc_reg <= ppc;
            
            // Create and push Fetch2Decode
            Fetch2Decode d;
	    d.pc    = pc;
	    d.ppc   = ppc;
            d.epoch = fEpoch;
            decodeFifo.enq(d);

        end
    endrule
    
    rule doDecode( cop.started && memReady && decodeFifo.notEmpty && regReadFifo.notFull );
        
        // Retrieve Fetch2Decode & Instruction
        let d = decodeFifo.first; decodeFifo.deq;
        let inst <- iMem.resp;
        
        // Decode Instruction
        let dInst = decode( inst );
        
        // Create and push Decode2RegRead
        Decode2RegRead rr;
        rr.pc    = d.pc;
        rr.ppc   = d.ppc;
        rr.dInst = dInst;
        rr.epoch = d.epoch;
        regReadFifo.enq(rr);
        
    endrule
    
    rule doRegRead( cop.started && memReady && regReadFifo.notEmpty && executeFifo.notFull );
        
        // Retrieve Decode2RegRead
        let rr = regReadFifo.first;
        
        // Ensure no dependencies
	Bool stall = sb.search1( rr.dInst.src1 ) || sb.search2( rr.dInst.src2 );
        if( !stall ) begin
            
            regReadFifo.deq;
            
            // Create and push RegRead2Execute
            RegRead2Execute e;
            e.pc     = rr.pc;
            e.ppc    = rr.ppc;
            e.dInst  = rr.dInst;
            e.rVal1  = rf.rd1( validRegValue( rr.dInst.src1 ) );
            e.rVal2  = rf.rd2( validRegValue( rr.dInst.src2 ) );
            e.copVal = cop.rd( validRegValue( rr.dInst.src1 ) );
            e.epoch  = rr.epoch;
            executeFifo.enq(e);
            
            // Update scoreboard
            sb.insert( rr.dInst.dst );
            
	end
        
    endrule
    
    rule doExecute( cop.started && memReady && executeFifo.notEmpty && memoryFifo.notFull );
        
        // Retrieve RegRead2Execute
        let e = executeFifo.first; executeFifo.deq;
        
        if(e.epoch != eEpoch) begin
            memoryFifo.enq( Exec2Commit{ iType: Unsupported, dst: Invalid, data: ?, addr: ? } );
        end else begin
            
            // Execute
            let eInst = exec( e.dInst, e.rVal1, e.rVal2, e.pc, e.ppc, e.copVal );
            if( eInst.iType == Unsupported ) begin
                $fwrite( stderr, "Executing unsupported instruction at pc: %x. Exiting\n", e.pc );
                $finish;
            end
            
            // Handle misprediction
            if( eInst.mispredict ) begin
                eEpoch <= !eEpoch;
                Redirect r;
                r.pc         = e.pc;
                r.nextPc     = eInst.addr;
                r.brType     = eInst.iType;
                r.taken      = eInst.brTaken;
                r.mispredict = eInst.mispredict;
                redirectFifo.enq(r);
            end
            
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
        if( c.iType == Ld ) dMem.req( MemReq{ op: Ld, addr: c.addr, data: c.data });
        if( c.iType == St ) dMem.req( MemReq{ op: St, addr: c.addr, data: c.data });
        
        // Push Exec2Commit
        writeBackFifo.enq(c);
    
    endrule
    
    rule doWriteBack( cop.started && memReady && writeBackFifo.notEmpty );
        
        // Retrieve Exec2Commit
        let c = writeBackFifo.first; writeBackFifo.deq;
        
        // Update c.data with memory data if applicable
        if( c.iType == Ld ) c.data <- dMem.resp;
            
        // Write Back
        if( isValid( c.dst ) && validValue( c.dst).regType == Normal ) begin
            rf.wr( validRegValue( c.dst ), c.data );
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
        pc_reg <= startpc;
    endmethod
    
    interface MemInit iMemInit = iMem.init;
    interface MemInit dMemInit = dMem.init;
    
endmodule

