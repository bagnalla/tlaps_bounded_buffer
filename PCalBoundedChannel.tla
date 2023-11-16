------------------------- MODULE PCalBoundedChannel -------------------------
EXTENDS Integers, Sequences, TLAPS

CONSTANT Msg, N

ASSUME N \in Nat \ {0}

(***************************************************************************
--algorithm BChan {
   variable ch = << >>;
   process (Send = "S") 
    { s: while (TRUE) 
          { await Len(ch) # N ;
            with (v \in Msg) { ch := Append(ch, v) }
          }
    }
   fair process (Rcv = "R") 
    { r: while (TRUE) 
          { await Len(ch) # 0 ;
            ch := Tail(ch)
          }
    }
}
 ***************************************************************************)
\* BEGIN TRANSLATION (chksum(pcal) = "be0f6a55" /\ chksum(tla) = "396318df")
VARIABLE ch

vars == << ch >>

ProcSet == {"S"} \cup {"R"}

Init == (* Global variables *)
        /\ ch = << >>

Send == /\ Len(ch) # N
        /\ \E v \in Msg:
             ch' = Append(ch, v)

Rcv == /\ Len(ch) # 0
       /\ ch' = Tail(ch)

Next == Send \/ Rcv

Wf == WF_vars(Rcv)

Spec == /\ Init /\ [][Next]_vars
        /\ Wf

\* END TRANSLATION

TypeOK == ch \in Seq(Msg)

Inv == /\ TypeOK
       /\ Len(ch) =< N

THEOREM RcvEnabled == TypeOK => (Len(ch) # 0 <=> ENABLED <<Rcv>>_vars)
  PROOF OMITTED

=============================================================================
\* Modification History
\* Last modified Wed Nov 15 20:09:50 EST 2023 by alex
\* Last modified Wed Jun 08 06:29:24 PDT 2011 by lamport
\* Created Sun Apr 17 11:40:12 PDT 2011 by lamport
