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
    Bool instEpoch;
} Fetch2Decode deriving (Bits, Eq);

typedef struct {
    Addr pc;
    Addr ppc;
    DecodedInst dInst;
    Bool instEpoch;
} Decode2RegRead deriving (Bits, Eq);

typedef struct {
    Addr pc;
    Addr ppc;
    DecodedInst dInst;
    Data rVal1;
    Data rVal2;
    Data copVal;
    Bool instEpoch;
} RegRead2Execute deriving (Bits, Eq);

(* synthesize *)
module mkProc(Proc);
    
    Reg#(Addr)     pc_reg <- mkReg(0);
    Btb#(6,8)      btb    <- mkBtb;
    RFile          rf     <- mkRFile;
    Scoreboard#(6) sb     <- mkBypassScoreboard;
    FPGAMemory     iMem   <- mkFPGAMemory();
    FPGAMemory     dMem   <- mkFPGAMemory();
    Cop            cop    <- mkCop;
    
    Reg#(Bool) fetchEpoch   <- mkReg(False);
    Reg#(Bool) executeEpoch <- mkReg(False);
    
    Bool memReady = iMem.init.done() && dMem.init.done();
    
    Fifo#(6, Redirect)        redirectFifo <- mkCFFifo();
    Fifo#(6, Fetch2Decode)    decodeFifo   <- mkCFFifo();
    Fifo#(6, Decode2RegRead)  regReadFifo  <- mkCFFifo();
    Fifo#(6, RegRead2Execute) executeFifo  <- mkCFFifo();
    Fifo#(6, ExecInst)        eInstFifo1   <- mkCFFifo();
    Fifo#(6, ExecInst)        eInstFifo2   <- mkCFFifo();
    
    rule doFetch(cop.started && memReady && decodeFifo.notFull());
        if(redirectFifo.notEmpty()) begin
            
            // Correct for misprediction
            let redirect_msg = redirectFifo.first(); redirectFifo.deq();
            pc_reg <= redirect_msg.nextPc;
            fetchEpoch <= !fetchEpoch;
            $display("Fetch: Mispredict");
            
            // Train BTB
            btb.update(redirect_msg.pc, redirect_msg.nextPc);
            
        end else begin
            
            // Fetch Instruction
            let pc  = pc_reg;
            let ppc = btb.predPc(pc);
            iMem.req(MemReq{ op: Ld, addr: pc, data: ? });
            
            // Update PC
            pc_reg <= ppc;
            
            // Create and push Fetch2Decode
            Fetch2Decode d;
	    d.pc        = pc;
	    d.ppc       = ppc;
            d.instEpoch = fetchEpoch;
            decodeFifo.enq(d);

        end
    endrule
    
    rule doDecode(cop.started && memReady && decodeFifo.notEmpty() && regReadFifo.notFull());
        
        // Retrieve Fetch2Decode & Instruction
        let d = decodeFifo.first(); decodeFifo.deq();
        let inst <- iMem.resp();
        
        // Create and push Decode2RegRead
        Decode2RegRead rr;
        rr.pc        = d.pc;
        rr.ppc       = d.ppc;
        rr.dInst     = decode(inst);
        rr.instEpoch = d.instEpoch;
        regReadFifo.enq(rr);
        
    endrule
    
    rule doRegRead(cop.started && memReady && regReadFifo.notEmpty());
        
        // Retrieve Decode2RegRead
        let rr = regReadFifo.first();
        
        // Ensure no dependencies
	if(!sb.search1(rr.dInst.src1) && !sb.search2(rr.dInst.src2)) begin
            
            // Create and push RegRead2Execute
            RegRead2Execute e;
            e.pc        = rr.pc;
            e.ppc       = rr.ppc;
            e.dInst     = rr.dInst;
            e.rVal1     = rf.rd1(validRegValue(rr.dInst.src1));
            e.rVal2     = rf.rd2(validRegValue(rr.dInst.src2));
            e.copVal    = cop.rd(validRegValue(rr.dInst.src1));
            e.instEpoch = rr.instEpoch;
            executeFifo.enq(e);
            
            // Update scoreboard
            sb.insert(rr.dInst.dst);
            
            // Consume Decode2RegRead
            regReadFifo.deq();
            
	end
        
    endrule
    
    rule doExecute(cop.started && memReady && executeFifo.notEmpty());
        
        // Retrieve RegRead2Execute
        let e = executeFifo.first(); executeFifo.deq();
        
        if(e.instEpoch != executeEpoch) begin
            
            // Kill mispredicted instruction
            sb.remove();
            $display("Execute: Kill instruction");
            
        end else begin
            
            // Execute
            let eInst = exec(e.dInst, e.rVal1, e.rVal2, e.pc, e.ppc, e.copVal);
            if(eInst.iType == Unsupported) begin
                $fwrite(stderr, "Executing unsupported instruction at pc: %x. Exiting\n", e.pc);
                $finish;
            end
            
            // Push eInst
            eInstFifo1.enq(eInst);
            
            // Handle misprediction
            if(eInst.mispredict) begin
                $display("Execute Mispredict: PC = %x", e.pc);
                redirectFifo.enq(Redirect{
                    pc: e.pc,
                    nextPc: eInst.addr,
                    brType: eInst.iType,
                    taken: eInst.brTaken,
                    mispredict: eInst.mispredict
                });
                executeEpoch <= !executeEpoch;
            end
            
        end
        
    endrule
    
    rule doMemory(cop.started && memReady && eInstFifo1.notEmpty());
        
        // Retrieve eInst
        let eInst = eInstFifo1.first(); eInstFifo1.deq();
        
        // Memory
        if(eInst.iType == Ld) begin
            dMem.req(MemReq{ op: Ld, addr: eInst.addr, data: ? });
        end else if(eInst.iType == St) begin
            dMem.req(MemReq{ op: St, addr: eInst.addr, data: eInst.data });
        end
        
        // Push eInst
        eInstFifo2.enq(eInst);
    
    endrule
    
    rule doWriteBack(cop.started && memReady && eInstFifo2.notEmpty());
        
        // Retrieve eInst
        let eInst = eInstFifo2.first(); eInstFifo2.deq();
        
        // Update eInst.data with memory data if applicable
        if(eInst.iType == Ld) eInst.data <- dMem.resp();
        
        // Write Back
        if(isValid(eInst.dst) && validValue(eInst.dst).regType == Normal) begin
            rf.wr(validRegValue(eInst.dst), eInst.data);
        end
        cop.wr(eInst.dst, eInst.data);
        sb.remove();
        
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

