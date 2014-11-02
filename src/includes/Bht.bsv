import Types::*;
import ProcTypes::*;
import RegFile::*;
import Vector::*;

typedef enum {
    StronglyTaken,
    WeaklyTaken,
    WeaklyNotTaken,
    StronglyNotTaken
} TakenState deriving ( Eq, Bits );

interface Bht#(numeric type n);
    method Bool predict(Addr pc);
    method Action train( Addr pc, Bool taken );
endinterface

module mkBht( Bht#(n) ) provisos ( Add#( n, a__, 32 ) ) ;
    
    Vector#( TExp#(n), Reg#( TakenState ) ) history <- replicateM( mkReg(StronglyTaken) );

    function Bit#(n) getIndex(Addr pc) = truncate(pc >> 2);
    
    method Bool predict(Addr pc);
        let state = history[getIndex(pc)];
        return ( ( state == StronglyTaken ) || ( state == WeaklyTaken ) );
    endmethod

    method Action train( Addr pc, Bool taken );
        let index = getIndex(pc);
        case (history[index])
            StronglyTaken    : history[index] <= taken ? StronglyTaken  : WeaklyTaken;
            WeaklyTaken      : history[index] <= taken ? StronglyTaken  : StronglyNotTaken;
            WeaklyNotTaken   : history[index] <= taken ? StronglyTaken  : StronglyNotTaken;
            StronglyNotTaken : history[index] <= taken ? WeaklyNotTaken : StronglyNotTaken;
        endcase
    endmethod
    
endmodule
