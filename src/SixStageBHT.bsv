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
    Bool mispredict;
} ExecuteRedirect deriving (Bits, Eq);

typedef struct {
    Addr nextPc;
    Bool eEp;
} DecodeRedirect deriving (Bits, Eq);

typedef struct {
    Addr pc;
    Addr ppc;
    Bool dEp;
    Bool eEp;
} Fetch2Decode deriving (Bits, Eq);

typedef struct {
    Addr pc;
    Addr ppc;
    DecodedInst dInst;
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
    
    Reg#(Addr)     pc_reg <- mkRegU;
    Btb#(6,8)      btb    <- mkBtb;
    Bht#(8)        bht    <- mkBht;
    RFile          rf     <- mkRFile;
    Scoreboard#(3) sb     <- mkBypassScoreboard;
    FPGAMemory     iMem   <- mkFPGAMemory();
    FPGAMemory     dMem   <- mkFPGAMemory();
    Cop            cop    <- mkCop;
    
    Reg#(Bool) feEp <- mkReg(False);
    Reg#(Bool) fdEp <- mkReg(False);
    Reg#(Bool) dEp  <- mkReg(False);
    Reg#(Bool) deEp <- mkReg(False);
    Reg#(Bool) eEp  <- mkReg(False);
    
    Fifo#(2, DecodeRedirect)  dRedirectFifo <- mkCFFifo;
    Fifo#(2, ExecuteRedirect) eRedirectFifo <- mkCFFifo;
    
    Fifo#(2, Fetch2Decode)    decodeFifo    <- mkCFFifo;
    Fifo#(2, Decode2RegRead)  regReadFifo   <- mkCFFifo;
    Fifo#(2, RegRead2Execute) executeFifo   <- mkCFFifo;
    Fifo#(2, Exec2Commit)     memoryFifo    <- mkCFFifo;
    Fifo#(2, Exec2Commit)     writeBackFifo <- mkCFFifo;
    
    Bool memReady = iMem.init.done() && dMem.init.done();
    
    rule doFetch( cop.started && memReady && decodeFifo.notFull );
        if( eRedirectFifo.notEmpty ) begin
            
            // Retrieve redirect information
            let r = eRedirectFifo.first; eRedirectFifo.deq;
            
            // Train BTB & BHT
            btb.update( r.pc, r.nextPc );
            if( r.iType != J ) bht.train( r.pc, r.taken );
            
            // Correct misprediction
            if( r.mispredict ) begin
                pc_reg <= r.nextPc;
                feEp   <= !feEp;
            end
            
        end else if( dRedirectFifo.notEmpty ) begin
            
            // Retrieve redirect information
            let r = dRedirectFifo.first; dRedirectFifo.deq;
            
            // Correct misprediction
            if( r.eEp == feEp ) begin
                pc_reg <= r.nextPc;
                fdEp   <= !fdEp;
            end
            
        end else begin
            
            // Fetch Instruction
            let pc  = pc_reg;
            let ppc = btb.predPc(pc);
            iMem.req( MemReq{ op: Ld, addr: pc, data: ? } );
            
            // Update PC
            pc_reg <= ppc;
            
            // Create and push Fetch2Decode
            Fetch2Decode d;
	    d.pc  = pc;
	    d.ppc = ppc;
            d.dEp = fdEp;
            d.eEp = feEp;
            decodeFifo.enq(d);

        end
    endrule
    
    rule doDecode( cop.started && memReady && decodeFifo.notEmpty && regReadFifo.notFull );
        
        // Retrieve Fetch2Decode & Instruction
        let d = decodeFifo.first; decodeFifo.deq;
        let inst <- iMem.resp;
        
        // Decode Instruction
        let dInst = decode(inst);
        
        // Predict Branch
        let nextPc  = d.pc + 4;
        let taken   = bht.predict(d.pc);
        if( dInst.iType == J ) nextPc[27:0] = validValue(dInst.imm)[27:0];
        else if( dInst.iType == Jr ) begin if( taken ) nextPc = d.ppc; end
        else if( dInst.iType == Br ) begin if( taken ) nextPc = nextPc + validValue(dInst.imm); end
        else nextPc = d.ppc;
        
        if( d.eEp != deEp ) begin
            
            deEp <= d.eEp; let next_dEp = d.dEp;
            
            // Create and push Decode2RegRead
            Decode2RegRead rr;
            rr.pc    = d.pc;
            rr.ppc   = nextPc;
            rr.dInst = dInst;
            rr.eEp   = d.eEp;
            regReadFifo.enq(rr);
            
            // Handle misprediction
            if( d.ppc != nextPc ) begin
                next_dEp = !next_dEp;
                DecodeRedirect dr;
                dr.nextPc = nextPc;
                dr.eEp    = d.eEp;
                dRedirectFifo.enq(dr);
            end
            
            dEp <= next_dEp;
        
        end else if( d.dEp == dEp ) begin
            
            // Create and push Decode2RegRead
            Decode2RegRead rr;
            rr.pc    = d.pc;
            rr.ppc   = nextPc;
            rr.dInst = dInst;
            rr.eEp   = d.eEp;
            regReadFifo.enq(rr);

            // Handle misprediction
            if( d.ppc != nextPc ) begin
                dEp <= !dEp;
                DecodeRedirect dr;
                dr.nextPc = nextPc;
                dr.eEp    = d.eEp;
                dRedirectFifo.enq(dr);
            end
            
        end
        
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
            e.eEp    = rr.eEp;
            executeFifo.enq(e);
            
            // Update scoreboard
            sb.insert( rr.dInst.dst );
            
	end
        
    endrule
    
    rule doExecute( cop.started && memReady && executeFifo.notEmpty && memoryFifo.notFull );
        
        // Retrieve RegRead2Execute
        let e = executeFifo.first; executeFifo.deq;
        
        if( e.eEp != eEp ) begin
            memoryFifo.enq( Exec2Commit{ iType: Unsupported, dst: Invalid, data: ?, addr: ? } );
        end else begin
            
            // Execute
            let eInst = exec( e.dInst, e.rVal1, e.rVal2, e.pc, e.ppc, e.copVal );
            if(eInst.iType == Unsupported) begin
                $fwrite( stderr, "Executing unsupported instruction at pc: %x. Exiting\n", e.pc );
                $finish;
            end
            
            // Handle misprediction
            if( eInst.mispredict ) eEp <= !eEp;
            
            // Handle branch
            if( eInst.iType == J  || eInst.iType == Jr || eInst.iType == Br ) begin
                ExecuteRedirect eR;
                eR.pc         = e.pc;
                eR.nextPc     = eInst.addr;
                eR.iType      = eInst.iType;
                eR.taken      = eInst.brTaken;
                eR.mispredict = eInst.mispredict;
                eRedirectFifo.enq(eR);
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
        pc_reg <= startpc;
    endmethod
    
    interface MemInit iMemInit = iMem.init;
    interface MemInit dMemInit = dMem.init;
    
endmodule

