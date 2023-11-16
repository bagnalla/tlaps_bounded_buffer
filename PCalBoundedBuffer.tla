------------------------ MODULE PCalBoundedBuffer --------------------------
(***************************************************************************)
(* This module contains a formal TLA+ proof of a result described in the   *)
(* TLA+ Hyperbook: that the bounded buffer algorithm specified in this     *)
(* module implements the bounded channel specified in module               *)
(* PCalBoundedChannel under a suitable refinement mapping.                 *)
(***************************************************************************)
EXTENDS Integers, Sequences, TLAPS

CONSTANT Msg, N

(***************************************************************************)
(* We give our assumption a name so it can be used in proofs.              *)
(***************************************************************************)
ASSUME NAssump == N \in Nat \ {0}

a (+) b == (a + b) % 2*N
a (-) b == (a - b) % 2*N

(***************************************************************************
--algorithm BBuf {
   variables buf \in [0..(N-1) -> Msg], p = 0, c = 0;
   process (Producer = "P") 
    { p1: while (TRUE) 
           { await p (-) c # N ;
             with (v \in Msg) { buf[p % N] := v }; 
             p := p (+) 1
           }
    }
   fair process (Consumer = "C") 
    { c1: while (TRUE) 
           { await p # c ;
             c := c (+) 1
           }
    }
}
 ***************************************************************************)
\* BEGIN TRANSLATION
VARIABLES buf, p, c

vars == << buf, p, c >>

ProcSet == {"P"} \cup {"C"}

Init == (* Global variables *)
        /\ buf \in [0..(N-1) -> Msg]
        /\ p = 0
        /\ c = 0

Producer == /\ p (-) c # N
            /\ \E v \in Msg:
                 buf' = [buf EXCEPT ![p % N] = v]
            /\ p' = p (+) 1
            /\ c' = c


Consumer == /\ p # c
            /\ c' = c (+) 1
            /\ UNCHANGED << buf, p >>


Next == Producer \/ Consumer

Wf == WF_vars(Consumer)

Spec == /\ Init /\ [][Next]_vars
        /\ Wf

\* END TRANSLATION
-----------------------------------------------------------------------------
(***************************************************************************)
(* It's convenient to name the set 0..(2*N-1) of values assumed by p and c *)
(* and to use this name in the type-correctness invariant.  Theorem        *)
(* provers work better when a subexpression can be replaced by a name, so  *)
(* we use more such auxiliary definitions when writing formulas for        *)
(* theorem provers to read than we do when the formulas are only going to  *)
(* be read by humans.                                                      *)
(***************************************************************************)
BufCtr == 0..(2*N-1)

PCInv == p (-) c \in 0..N

TypeOK == /\ buf \in [0..N-1 -> Msg]
          /\ p \in BufCtr
          /\ c \in BufCtr

Inv == TypeOK /\ PCInv

(***************************************************************************)
(* Currently, the theorem provers know nothing about the modulus operator  *)
(* % , so we need to give it some facts about this operator.  We start by  *)
(* assuming the following two facts.  TLC checks them in a few seconds     *)
(* when Int is replaced by the set -50..50 and Nat \ {0} by the set 1..20. *)
(***************************************************************************)
LEMMA ModDef == \A i \in Int, j \in Nat \ {0} :
                   /\ i % j \in 0..(j-1)
                   /\ i \in 0..(j-1) => i % j = i
                   /\ i % j = (i + j) % j
                   /\ i % j = (i - j) % j
  <1> SUFFICES ASSUME NEW i \in Int, NEW j \in Nat \ {0}
               PROVE  /\ i % j \in 0..(j-1)
                      /\ i \in 0..(j-1) => i % j = i
                      /\ i % j = (i + j) % j
                      /\ i % j = (i - j) % j
    OBVIOUS
  <1>1. i % j \in 0..(j-1)
    OBVIOUS
  <1>2. i \in 0..(j-1) => i % j = i
    OBVIOUS
  <1>3. i % j = (i + j) % j
    PROOF OMITTED
  <1>4. i % j = (i - j) % j
    PROOF OMITTED
  <1>5. QED
    BY <1>1, <1>2, <1>3, <1>4

LEMMA ModMod == \A i, j \in Int, n \in Nat \ {0} :
                    /\ ((i%n) + j)%n = (i+j)%n
                    /\ (i - (j%n))%n = (i-j)%n
PROOF OMITTED

(***************************************************************************)
(* This proof was originally written using a different back-end prover     *)
(* than SMT for arithmetical reasoning.  That prover could not deduce 2*N  *)
(* \in Int from NAssump.  To work around that problem, I introduced the    *)
(* definition of K and assumed lemma KDef.  The entire proof can probably  *)
(* be simplified because the SMT back-end is smarter than the previous     *)
(* one.                                                                    *)
(***************************************************************************)
K == 2*N
LEMMA KDef == K = N + N
BY NAssump DEF K


(***************************************************************************)
(* The following seven lemmas (through Lemma ModN1) are simple facts about *)
(* the constants K and N and the operators (+) and (-).  They assert       *)
(* results that I found useful in proving the invariance of Inv.  These    *)
(* results are all obvious arithmetic facts.  Checking them with TLC       *)
(* should provide enough confidence in their correctness that it's         *)
(* probably not worth proving them.  If you were writing the proof, you    *)
(* certainly wouldn't bother to prove them until you were certain that the *)
(* algorithm was correct.  Proving them does provide a good "warm-up       *)
(* exercise" before attacking the main proof, and reading the proofs will  *)
(* help you learn how to use TLAPS.                                        *)
(*                                                                         *)
(* We being with some simple results about K and BufCtr.  Their proofs are *)
(* simple, using only definition expansion and some simple applications of *)
(* SMT.                                                                    *)
(***************************************************************************)
LEMMA KFacts == K \in Int /\ K > N
<1>1. N + N \in Int /\ N + N > N
  BY NAssump, SMT
<1>2. QED
  BY <1>1, KDef

LEMMA KBufCtr == BufCtr = 0..(K-1)
BY DEF K, BufCtr

LEMMA 1InBufCtr == 1 \in BufCtr
<1>1. 1 \in 0..(K-1)
  BY NAssump, KFacts, SMT
<1>2. QED
  BY <1>1, KBufCtr

LEMMA OPlusDef == \A a, b \in BufCtr :
                     a (+) b = IF a + b < 2*N THEN a + b
                                              ELSE a + b - 2*N
                                              
<1> SUFFICES ASSUME NEW a \in 0..(K-1), NEW b \in 0..(K-1)
             PROVE  (a + b) % K = IF a + b < K THEN a + b
                                               ELSE a + b - K
  BY KFacts, KBufCtr DEF K, (+)
<1>1. /\ a \in Int
      /\ b \in Int
      /\ a + b \in Int
      /\ K \in Nat \ {0}
      /\ \/ /\ a + b < K
            /\ a + b \in 0..(K-1)
         \/ /\ ~(a + b < K)
            /\ a + b - K \in 0..(K-1)
      /\ (a+b)-K = a + b - K
      /\ (a+b)-K \in Int
  BY NAssump, SMT DEF K
(***************************************************************************)
(* The following two CASE steps are left unnumbered mainly to avoid having *)
(* to write the statement number everywhere CASE assumption is being used  *)
(* inside their proofs.  This also avoids having to write those step       *)
(* numnbers in the final QED step.                                         *)
(*                                                                         *)
(* <1>1!5 is the 5th operand of the expression <1>1.  Since <1>1 is a list *)
(* conjunction, which is considered to be a single operator applied to its *)
(* 7 conjuncts, <1>1!5 is the 5th conjunct.  Similarly, because <1>1!5 is  *)
(* a list disjunction, <1>1!5!1 is the first disjunct of that list.        *)
(***************************************************************************)
<1> CASE <1>1!5!1
  BY <1>1, ModDef
<1> CASE <1>1!5!2
  (*************************************************************************)
  (* Examine just the high-level proof of this CASE statement by clicking  *)
  (* on the statement and executing the Show Children Only command         *)
  (* (control+g control+c).  Observe steps <2>2 and <2>3.  In those steps, *)
  (* the "@" stands for the right-hand side of the equality in the         *)
  (* preceding step at the same level.  Thus, these two steps are          *)
  (* abbreviations for                                                     *)
  (*                                                                       *)
  (*    <2>2. ((a + b) - K)% K = (a + b) - K                               *)
  (*    <2>3. (a + b) - K = a + b - K                                      *)
  (*                                                                       *)
  (* This "@" convention is convenient for writing proofs containing a     *)
  (* sequence of equalities and inequalities, a sequence of implications,  *)
  (* or any sequence of (binary) infix relations.  Even in this case,      *)
  (* where the use of "@" does not make the steps much shorter, it makes   *)
  (* them easier to read because it's easy to see that they are a sequence *)
  (* of equalities.                                                        *)
  (*************************************************************************)
  <2>1. (a + b) % K = ((a + b) - K)% K 
    BY <1>1, ModDef
  <2>2. @ = (a + b) - K
     BY <1>1, ModDef
  <2>3. @ = a + b - K
    BY <1>1
  <2>4. QED
    BY <2>1, <2>2, <2>3 \* <2>4
<1>2. QED
  BY <1>1

                                          
LEMMA OMinusDef == \A a, b \in BufCtr :
                     a (-) b = IF a - b >= 0 THEN a - b
                                             ELSE a - b + 2*N
(***************************************************************************)
(* This proof is obtained by copying the proof of OPlus and making the     *)
(* appropriate changes.                                                    *)
(*                                                                         *)
(* Note that a - b + 2*N is parsed as (a - b) + @*N .                      *)
(***************************************************************************)
<1> SUFFICES ASSUME NEW a \in 0..(K-1), NEW b \in 0..(K-1)
             PROVE  (a - b) % K = IF a - b >= 0 THEN a - b
                                                ELSE a - b + K
  BY KFacts, KBufCtr DEF K, (-)
<1>1. \A k \in Int:
         (k > N) => \A aa, bb \in 0..(k-1) :
                      /\ aa \in Int
                      /\ bb \in Int
                      /\ aa - bb \in Int
                      /\ k \in Nat \ {0}
                      /\   \/ /\ aa - bb >= 0
                              /\ aa - bb \in 0..(k-1)
                           \/ /\ ~(aa - bb >= 0)
                              /\ aa - bb + k \in 0..(k-1)
                      /\ aa - bb + k \in Int
  BY NAssump, SMT
<1>2. /\ a \in Int
      /\ b \in Int
      /\ a - b \in Int
      /\ K \in Nat \ {0}
      /\ \/ /\ a - b >= 0
            /\ a - b \in 0..(K-1)
         \/ /\ ~(a - b >= 0)
            /\ a - b + K \in 0..(K-1)
      /\ (a-b)+K \in Int
  BY <1>1, KFacts
<1> CASE <1>2!5!1
  BY <1>2, ModDef
<1> CASE <1>2!5!2
  <2>1. (a - b) % K = (a - b + K)% K 
    BY <1>2, ModDef
  <2>2. @ = a - b + K
     BY <1>2, ModDef
  <2>4. (a - b) % K = (a - b + K) 
    BY <2>1, <2>2 \* , <2>3
  <2>5. QED
    BY <2>4
<1> QED
  BY <1>2 

(***************************************************************************)
(* Click on the name ModRules in the following lemma and execute the Show  *)
(* Uses command (F6) to highlight all uses of the Lemma.  You can use the  *)
(* F7 and F8 keys to cycle through all the uses.  You will find that the   *)
(* lemma is used only in the proof of Lemma ProducerConsumer Use the Goto  *)
(* Declaration command (F3) to return to the lemma.                        *)
(***************************************************************************)
LEMMA ModRules == \A a, b \in BufCtr :
                     /\ (a (+) 1) (-) b = (a (-) b) (+) 1
                     /\ a (-) (b (+) 1) = (a (-) b) (-) 1
<1> SUFFICES ASSUME NEW a \in BufCtr, NEW b \in BufCtr
             PROVE  /\ (((a + 1) % K) - b) % K = (((a - b)%K) + 1) % K
                    /\ (a - ((b + 1)%K)) % K = (((a - b)%K) - 1) % K
  BY DEF (+), (-), K
<1>1. /\ a \in Int 
      /\ b \in Int /\ -b \in Int 
      /\ 1 \in Int /\ -1 \in Int
      /\ K \in Int /\ K \in Nat \ {0}
  BY KBufCtr, KFacts, NAssump, SMT 
<1>2. (((a + 1) % K) - b) % K = (((a - b)%K) + 1) % K
  (*************************************************************************)
  (* In this proof, we need to apply some simple arithmetical reasoning to *)
  (* expressions containing (a+1)%K and (a-b)%K that use only the fact     *)
  (* that those two values are integers.  One way to do this is to (a)     *)
  (* prove that these two quantities are integers, (b) use SMT to prove    *)
  (* the necessary results for arbitrary integers i and j, and (c) use the *)
  (* ordinary back-end provers to deduce the desired result from (a) and   *)
  (* (b).  Another method is to (i) define i and j to be these two         *)
  (* quantities, (ii) prove that i and j are integers, (iii) hide the      *)
  (* definitions of i and j, and (iv) let SMT prove the desired result,    *)
  (* using (ii).  The definitions of i and j can then be used as needed.   *)
  (* This is what we do, except we use the more helpful names a1K and abK  *)
  (* instead of i and j.                                                   *)
  (*************************************************************************)
  <2> DEFINE a1K == (a + 1) % K
             abK == (a - b) % K
  <2>1. (a1K - b) % K = (a + 1 - b) % K
    <3>1. a+1 \in Int /\ -b \in Int
      BY <1>1, SMT
    <3>2. a1K \in 0..(K-1)
      BY <1>1, <3>1, ModDef
    <3> HIDE DEF a1K
    <3>3. a1K - b = a1K + (-b)
      BY <3>2, KFacts, <1>1, SMT
    <3>4. (a1K + (-b)) % K = ((a+1) + (-b)) % K
      BY <1>1, <3>1, ModMod, SlowerZenon  DEF a1K
    <3>5. (a+1) + (-b) = a + 1 - b
      BY <1>1, SMT
    <3>6. QED
      BY <3>3, <3>4, <3>5
  <2>2. (abK + 1) % K = (a - b + 1) % K
    <3>1. a-b \in Int
      BY <1>1, SMT
    <3>2. QED
      BY <1>1, <3>1, ModMod 
  <2>3. a + 1 - b = a - b + 1
    BY <1>1, SMT
  <2>4. QED
    BY <2>1, <2>2, <2>3
<1>3. (a - ((b + 1)%K)) % K = (((a - b)%K) - 1) % K
  <2> DEFINE b1K == (b+1)%K
             abK == (a-b)%K
  <2>1. (a - b1K) % K = (a - (b+1)) % K
    <3>1. b+1 \in Int
      BY <1>1, SMT
    <3>2. QED
      BY <3>1, <1>1, ModMod, SlowestZenon
  <2>2. (abK - 1) % K = ((a-b) - 1) % K
    <3>1. a-b \in Int
      BY <1>1, SMT
    <3>2. abK \in 0..(K-1)
      BY <1>1, <3>1, ModDef
    <3>3. -1 \in Int  /\ K \in Nat \ {0}
      BY <1>1
    <3>4. (abK + (-1)) % K = (a-b + (-1)) % K
      BY <3>1, <3>3, ModMod 
    <3> HIDE DEF abK
    <3>5. /\ abK - 1 = abK + (-1)
          /\ a-b + (-1) = (a-b) - 1
      BY <1>1, <3>2, SMT   
    <3>56. QED
      BY <3>4, <3>5
  <2>3. a - (b+1) = (a-b) - 1
    BY <1>1, SMT
  <2>4. QED
    BY <2>1, <2>2, <2>3
<1>4. QED
  BY <1>2, <1>3
           
(***************************************************************************)
(* The next lemma is a simple consequence of assumption NAssump and of     *)
(* lemma ModDef.  Telling a prover to use the lemma rather than to use     *)
(* ModDef and NAssump simplifies the prover's task and can make the        *)
(* difference between a proof succeeding and failing.                      *)
(***************************************************************************)
LEMMA ModN1 == \A a \in Int : a % N \in 0..(N-1)
BY NAssump, ModDef

(***************************************************************************)
(* The following lemma is an important part of proving the correctness of  *)
(* the algorithm.  It shows that the Producer and Consumer actions make    *)
(* the correct changes to p (-) c, which is the number of messages in the  *)
(* channel.                                                                *)
(***************************************************************************)
LEMMA ProduceConsume == /\ Inv /\ Producer => (p' (-) c') = (p (-) c) + 1
                        /\ Inv /\ Consumer => /\ (p (-) c) # 0
                                              /\ (p' (-) c') = (p (-) c) - 1
<1>1. ASSUME Inv
      PROVE  /\ p \in 0..(K-1)
             /\ c \in 0..(K-1)
  BY <1>1, KBufCtr DEF Inv, TypeOK
<1>2. ASSUME Inv, Producer
      PROVE  (p' (-) c') = (p (-) c) + 1
  <2> USE Inv, Producer
  <2> SUFFICES (p (+) 1) (-) c = (p (-) c) + 1
    BY DEF Producer
  <2>1. (p (+) 1) (-) c = (p (-) c) (+) 1
    BY <1>1, KBufCtr, ModRules
  <2>2. ASSUME NEW i \in 0..N
        PROVE  /\ i \in 0..(K-1)
               /\ i # N => i+1 < K
     BY KFacts, NAssump, SMT 
  <2>3. /\ (p (-) c) \in 0..(K-1)
        /\ (p (-) c) + 1 < K
    BY <2>2 DEF Producer, Inv, PCInv
  <2>4. (p (-) c) (+) 1 = (p (-) c) + 1
    BY <2>3, 1InBufCtr, KBufCtr, OPlusDef DEF K
  <2>5. QED
    BY <2>1, <2>4
<1>3. ASSUME Inv, Consumer
      PROVE  /\ (p' (-) c') = (p (-) c) - 1
             /\ (p (-) c) # 0
  <2> USE Inv, Consumer
  <2> SUFFICES /\ p (-) (c (+) 1) = (p (-) c) - 1
               /\ (p (-) c) # 0
    BY DEF Consumer
  <2>1. p (-) (c (+) 1) = (p (-) c) (-) 1
    BY <1>1, KBufCtr, ModRules
  <2>2. ASSUME NEW i \in 0..N
        PROVE  /\ i \in 0..(K-1)
               /\ i # 0 => (i - 1) >= 0
     BY KFacts, NAssump, SMT 
  <2>3. p (-) c # 0
    <3>1. CASE p - c >= 0
      <4>1. p (-) c = p - c
         BY <3>1, <1>1, KBufCtr, OMinusDef
      <4>2. p - c # 0
        BY <3>1, <1>1, p  \in  0 .. K-1, c  \in  0 .. K-1, KFacts, SMT DEF Consumer
      <4>3. QED
        BY <4>1, <4>2
    <3>2. CASE ~(p - c >= 0)
      <4>1. p (-) c = p - c + K
        BY <3>2, <1>1, KBufCtr, OMinusDef DEF K
      <4>2. ASSUME NEW k \in Int,
                       p \in 0..(k-1),
                       c \in 0..(k-1)
            PROVE  p - c + k # 0 
         BY <4>2, <3>2, SMT
      <4>3. p - c + K # 0
        BY <4>2, KFacts, <1>1
      <4>4. QED
        BY <4>1, <4>3
    <3>3. QED
      BY <3>1, <3>2
  <2>4. /\ (p (-) c) \in 0..(K-1)
        /\ (p (-) c) - 1 >= 0
    BY <2>2, <2>3 DEF Consumer, Inv, PCInv
  <2>5. (p (-) c) (-) 1 = (p (-) c) - 1
    BY <2>4, 1InBufCtr, KBufCtr, OMinusDef DEF K
  <2>6. QED
    BY <2>1, <2>3, <2>5
<1>4. QED
  BY <1>2, <1>3

USE DEF Inv
THEOREM Invariance == Init /\ [][Next]_vars => []Inv
<1>1. Init => Inv
  <2> SUFFICES ASSUME Init PROVE Inv
    OBVIOUS
  <2> USE DEF Init, Inv
  <2>1. 0 \in BufCtr
      BY NAssump, SMT DEF BufCtr
  <2>2. TypeOK
    BY <2>1 DEF TypeOK
  <2>3. PCInv
    <3>1. 0 (-) 0 = 0
      <4>1. 0 - 0 = 0 /\ 0 >= 0
        BY SMT
           (****************************************************************)
           (* Isabelle knows enough about numbers to be able to prove this *)
           (* as well.  However, it isn't smart enough to figure out by    *)
           (* itself that it needs to prove these facts to prove <3>1, so  *)
           (* it can't prove <3>1 in a single step.                        *)
           (****************************************************************)
      <4>2. QED
        BY <2>1, <4>1, OMinusDef 
    <3>2. 0 \in 0..N
      BY NAssump, SMT
    <3> QED
      BY <3>1, <3>2 DEF PCInv
  <2>4. QED
     BY <2>2, <2>3
<1>2. Inv /\ [Next]_<<buf, p, c>> => Inv'
  <2> SUFFICES ASSUME Inv, [Next]_<<buf, p, c>>
               PROVE  Inv'
    OBVIOUS
  <2>1. CASE Next
    (***********************************************************************)
    (* The next step will be needed to prove that the Producer and         *)
    (* Consumer actions preserve the invariance of  p(+)1 \in BufCtr  and  *)
    (* of  c(+)1 \in BufCtr, respectively.                                 *)
    (***********************************************************************)
    <3>1. ASSUME NEW i \in BufCtr
          PROVE  i (+) 1 \in BufCtr
      <4>1. \/ /\ i+1 < K
               /\ i+1 \in 0..(K-1)
            \/ /\ ~(i+1 < K)
               /\ i+1-K \in 0..(K-1)
        <5>1. i \in 0..(K-1)
          BY <3>1 DEF BufCtr, K
        <5>2. QED
          BY <5>1, KFacts, SMT
      <4>2. CASE i+1 < K
        <5>1. i (+) 1 = i+1
          BY <4>2, <3>1, 1InBufCtr, KBufCtr, OPlusDef DEF K
        <5>2. QED
          BY <5>1, <4>1, <4>2, KBufCtr
      <4>3. CASE ~(i+1 < K)
        <5>1. i (+) 1 = i+1-K
          BY <4>3, <3>1, 1InBufCtr, KBufCtr, OPlusDef DEF K
        <5>2. QED
          BY <5>1, <4>1, <4>3, KBufCtr
      <4>4. QED
        BY <4>2, <4>3
    <3>2. CASE Producer
      <4> SUFFICES ASSUME Producer PROVE Inv'
        BY <3>2
      <4>1. PICK v \in Msg : buf' = [buf EXCEPT ![p % N] = v]
        BY DEF Producer
      <4>2. TypeOK'
        <5>1. buf' \in [0..(N-1) -> Msg]
          BY <4>1, ModN1 DEF Inv, TypeOK
        <5>2. p (+) 1 \in BufCtr
          BY <3>1 DEF Inv, TypeOK
        <5>3. QED
          BY <5>1, <5>2 DEF Producer, Inv, TypeOK
      <4>3. PCInv'
        <5> SUFFICES (p (-) c) + 1 \in 0..N
          BY ProduceConsume DEF PCInv
        <5>1. \A i \in 0..N : i # N => i+1 \in 0..N
          BY NAssump, SMT
        <5>2. QED
          BY <5>1 DEF Inv, PCInv, Producer
      <4>4. QED
        BY <4>2, <4>3 DEF Inv
    <3>3. CASE Consumer
      <4>1. TypeOK'
          BY <3>1, <3>3 DEF Consumer, Inv, TypeOK 
      <4>2. PCInv'
        <5> SUFFICES (p (-) c) - 1 \in 0..N
          BY <3>3, ProduceConsume DEF PCInv
        <5>1. \A i \in 0..N : i # 0 => i-1 \in 0..N
          BY NAssump, SMT
        <5>2. QED
          BY <3>3, <5>1, ProduceConsume DEF Inv, PCInv, Consumer
      <4>3. QED
        BY <4>1, <4>2 DEF Inv
    <3>4. QED
      BY <2>1, <3>2, <3>3 DEF Next
  <2>2. CASE UNCHANGED <<buf, p, c>>
    BY <2>2 DEF Inv, TypeOK, PCInv
  <2>3. QED
    BY <2>1, <2>2
  (*************************************************************************)
  (* This follows from <1>1 and <1>2 by application of the standard TLA+   *)
  (* proof rule:                                                           *)
  (*                                                                       *)
  (*       I /\ [N]_v => I'                                                *)
  (*     -------------------                                               *)
  (*     I /\ [][N]_v => []I                                               *)
  (*************************************************************************)
<1> HIDE DEF Inv
<1>3. (Inv /\ [][Next]_vars) => []Inv
  BY <1>2, PTL DEF vars
<1>4. QED
  BY <1>1, <1>3 DEF Spec
  
-----------------------------------------------------------------------------
(***************************************************************************)
(* The following definition of chBar differs from the one in the           *)
(* Hyperbook.  It was the definition I first wrote and with which I proved *)
(* correctness of the algorithm: the theorem                               *)
(*                                                                         *)
(*    Spec => C!Spec                                                       *)
(*                                                                         *)
(* where C!Spec is defined here to be the specification obtained from that *)
(* in module PCalBoundedChannel under the refinement mapping ch <- chBar.  *)
(***************************************************************************)
chBar == [i \in 1..(p (-) c) |-> buf[(c + i - 1) % N]]
C == INSTANCE PCalBoundedChannel WITH ch <- chBar

(***************************************************************************)
(* I later decided that the definition in the Hyperbook is more            *)
(* transparent.  Instead of changing the definition of chBar and the       *)
(* proof, it was much easier to use what I had already proved to prove the *)
(* theorem from the Hyperbook.  The definition of newChBar below is the    *)
(* same as the definition of chBar in the Hyperbook.  With the following   *)
(* defintions, correctness of the algorithm under the refinement mapping   *)
(* of the Hyperbook is therefore expressed by the theorem                  *)
(*                                                                         *)
(*    Spec => NC!Spec                                                      *)
(*                                                                         *)
(* which is proved later.                                                  *)
(***************************************************************************)
newChBar == [i \in 1..(p (-) c) |-> buf[(c (+) (i - 1)) % N]]
NC == INSTANCE PCalBoundedChannel WITH ch <- newChBar

(***************************************************************************)
(* First comes the proof of Spec => C!Spec.  We begin with two additional  *)
(* lemmas about modular arithmetic.  The first two are proved from earlier *)
(* results.                                                                *)
(***************************************************************************)
LEMMA ModN2 == \A a \in 0..(N-1) : a % N = a
<1> SUFFICES ASSUME NEW a \in 0..(N-1)
             PROVE  a % N = a
  OBVIOUS
<1> a \in Int
  BY NAssump, SMT
<1> QED
  BY NAssump, ModDef

LEMMA ModN3 == \A a, b \in Int : 
                  /\ (a + b) % N = ((a % N) + (b % N)) % N
                  /\ (a - b) % N = ((a % N) - (b % N)) % N
<1> SUFFICES ASSUME NEW a \in Int, NEW b \in Int
             PROVE  /\ (a + b) % N = ((a % N) + (b % N)) % N
                    /\ (a - b) % N = ((a % N) - (b % N)) % N
  OBVIOUS
<1> DEFINE aN == a % N
           bN == b % N
<1>1. (aN \in Int) /\ (bN \in Int)
  <2>1. (aN \in 0..(N-1)) /\ (bN \in 0..(N-1))
    BY NAssump, ModDef
  <2>2. \A x : x \in 0..(N-1) => x \in Int
    BY NAssump, SMT
  <2>3. QED
    BY <2>1, <2>2
<1> HIDE DEF aN, bN
<1>2. (a + b) % N = (aN + bN) % N
  <2>1. (aN + bN) % N = (a + bN) % N
    BY <1>1, NAssump, ModMod DEF aN
  <2>2. @ = (bN + a) % N
    <3>1. a + bN = bN + a
      BY <1>1, SMT
    <3>2. QED
      BY <3>1
  <2>3. @ = (b + a) % N
    BY NAssump, ModMod DEF bN
  <2>4. @ = (a + b) % N
    <3>1. a+b = b+a
      BY SMT
    <3>2. QED
      BY <3>1
  <2>5. QED 
    BY <2>1, <2>2, <2>3, <2>4
<1>3. (a - b) % N = (aN - bN) % N
  <2>1. (aN - bN)% N = (aN - b) % N
    BY <1>1, NAssump, ModMod DEF bN
  <2>2. @ = (aN + (-b)) % N
    <3>1. aN - b = aN + (-b)
      BY <1>1, SMT
    <3>2. QED
      BY <3>1
  <2>3. @ = (a + (-b)) % N
    <3>1. -b \in Int
      BY SMT
    <3>2. QED
      BY NAssump, <3>1, ModMod DEF aN
  <2>4. @ = (a - b) % N
    <3>1 a + (-b) = a - b
      BY SMT
    <3>2. QED
      BY <3>1
  <2>5. QED
    BY <2>1, <2>2, <2>3, <2>4  
<1>4. QED
  BY <1>2, <1>3 DEF aN, bN


(***************************************************************************)
(* The following result about modular arithemtic is fundamental to why the *)
(* algorithm is correct.  We assume its correctness, which TLC checks in a *)
(* couple of seconds for all values of N in 0..20 and of i in -50..50.     *)
(***************************************************************************)
LEMMA Mod2N == \A i \in Int : (i % 2*N) % N = i % N
PROOF OMITTED

LEMMA SeqDef == \A S : 
                  \A n \in Nat :
                    \A f \in [1..n -> S] :
                       f \in Seq(S) /\ Len(f) = n
  OBVIOUS

LEMMA EmptySeq == \A S : \A s \in Seq(S) : Len(s) = 0 <=> s = << >>
  OBVIOUS

(***************************************************************************)
(* The next two lemmas assert properties of the operators on sequences     *)
(* defined in the Sequences module.  These results all follow easily from  *)
(* the operators' definitions.  However, the back-end provers do not yet   *)
(* have any built-in knowledge of these operators, and TLAPS does not      *)
(* allow us to expand the definitions of any of them in a DEF clause.  We  *)
(* therefore assume them to be true.  The results are obvious, and TLC has *)
(* checked them for trivial mistakes.                                      *)
(***************************************************************************)

LEMMA AppendDef == \A S : 
                     \A s \in Seq(S) :
                       \A e : Append(s, e) = 
                                [i \in 1..(Len(s)+1) |-> 
                                   IF i = Len(s)+1 THEN e ELSE s[i]]
PROOF OMITTED

LEMMA TailDef == \A S : 
                   \A s \in Seq(S) :
                     (Len(s) # 0) => 
                        Tail(s) = [i \in 1..(Len(s)-1) |-> s[i+1]]
PROOF OMITTED

(* Spec implies weak fairness of C!Rcv. *)
THEOREM WFC == Spec => C!Wf
PROOF OMITTED

(* C!Spec implies weak fairness of NMC!Rcv. *)
THEOREM WFNC == C!Spec => NC!Wf
PROOF OMITTED

THEOREM ChBarImpl == Spec => C!Spec
<1>1. Init => C!Init
  <2> SUFFICES ASSUME Init
               PROVE C!Init
    OBVIOUS
  <2>1. 0 (-) 0 = 0
    <3>1. ASSUME NEW k \in Int, k > N
          PROVE  /\ 0 \in 0..(k-1)
                 /\ 0 - 0 = 0
                 /\ 0 - 0 >= 0
      BY <3>1, NAssump, SMT 
    <3>2. QED
      BY <3>1, KFacts, KBufCtr, OMinusDef
  <2>2. chBar \in [1..0 -> Msg]
    <3>1. 1..0 = {}
      BY SMT
    <3>2. \A i \in 1..0 :  buf[(c + i - 1) % N] \in Msg
      BY <3>1
    <3>3. QED
      BY <2>1, <3>2 DEF chBar, Init
  <2>3. chBar \in Seq(Msg) /\ Len(chBar) = 0
    BY <2>2, SeqDef
  <2>4. QED
    BY <2>3, EmptySeq DEF C!Init
<1>2. Inv /\ Next => C!Next \/ UNCHANGED chBar
  <2> SUFFICES ASSUME Inv, Next
      PROVE    C!Next
    OBVIOUS
  <2>1. /\ p \in 0..(K-1)
        /\ c \in 0..(K-1)
        /\ p \in Int
        /\ c \in Int
    <3>1. /\ p \in 0..(K-1)
          /\ c \in 0..(K-1)
      BY KBufCtr DEF Inv, TypeOK
    <3>2. \A k \in Int: \A pp \in 0..(k-1), cc \in 0..(k-1) :
            pp \in Int /\ cc \in Int
      BY SMT
    <3>3. QED
      BY <3>1, <3>2, KFacts   
  <2>2. chBar \in [1..(p (-) c) -> Msg]
    <3>1. \A i \in 1..(p (-) c) : c + i - 1 \in Int
      <4>1. \A k \in Int :
              \A pmc \in 0..N : 
               \A i \in 1..pmc : 
                  c \in 0..(k-1) => c + i - 1 \in Int
        BY NAssump, <2>1, SMT
      <4>2. QED
        BY <4>1, KFacts, KBufCtr DEF Inv, TypeOK, PCInv
    <3>2. \A i \in 1..(p (-) c) :  buf[(c + i - 1) % N] \in Msg
      BY <3>1, ModN1 DEF Inv, TypeOK
    <3>3. QED
      BY <3>2 DEF chBar
  <2>3. /\ chBar \in Seq(Msg)
        /\ Len(chBar) = p (-) c
    <3>1. \A pmc \in 0..N : pmc \in Nat
      BY NAssump, SMT
    <3>3. QED
      BY <2>2, <3>1, SeqDef DEF Inv, PCInv      
  <2>4. ASSUME Producer
        PROVE  C!Send
    <3> USE Producer
    <3>1. PICK v \in Msg : buf' = [buf EXCEPT ![p % N] = v]
      BY DEF Producer
    <3>2. SUFFICES chBar' = Append(chBar, v)
      BY <2>3 DEF Producer, C!Send
    <3>3. Append(chBar, v) = 
           [i \in 1..((p(-)c)+1) |->
             IF i = (p(-)c)+1 THEN v ELSE chBar[i]]
      <4> SUFFICES
            Append(chBar, v) = 
              [i \in 1..(Len(chBar)+1) |->
                  IF i = Len(chBar)+1 THEN v ELSE chBar[i]]
        BY <2>3
      <4> QED 
        BY <2>3, AppendDef
    <3>4. /\ p % N = (c + (((p(-)c)+1) - 1)) % N
          /\ \A i \in 1..((p(-)c)+1) :
                /\ (c + (i - 1)) % N \in 0..(N-1)
                /\ (i = (p(-)c)+1) <=> ((c + (i - 1)) % N = p % N)
      <4>1. p (-) c \in 0..(N-1)
        <5>1. \A pmc \in 0..N : pmc # N => pmc \in 0..(N-1)
          BY NAssump, SMT
        <5>2. QED
          BY <5>1 DEF Producer, Inv, PCInv
      <4> DEFINE pmc == p (-) c
      <4>2. p % N = (c + ((pmc+1) - 1)) % N
        <5>1. /\ pmc \in Int
              /\ p \in Int
              /\ c \in Int
              /\ p-c \in Int
          <6>1. /\ \A i \in 0..N : i \in Int
                /\ \A k \in Int : \A pp \in 0..(k-1), cc \in 0..(k-1) :
                     pp \in Int  /\  cc \in Int /\ (pp-cc) \in Int
            BY SMT      
          <6>2. QED
            BY <6>1, <2>1, KFacts DEF Inv, PCInv
        <5> HIDE DEF pmc
        <5>2. \A i \in Int : (i+1) - 1 = i
          BY SMT
        <5>3.  (c + ((pmc+1) - 1)) % N = (c + pmc) % N 
          BY <5>1, <5>2
        <5>4. @ = ((c % N) + (pmc % N)) % N
          BY ModN3, <5>1
        <5>5. @ = ((c % N) + ((p-c) % N)) % N
          BY Mod2N, <5>1 DEF pmc, (-)
        <5>6. @ = (c + (p-c)) % N
          BY ModN3, <5>1
        <5>7. @ = p % N
          <6>1. c + (p-c) = p
            BY <5>1, SMT
          <6>2. QED
            BY <6>1
        <5>8. QED
          BY <5>3, <5>4, <5>5, <5>6, <5>7
      <4> SUFFICES ASSUME NEW i \in 1..(pmc+1)
                   PROVE  /\ (c + (i - 1)) % N \in 0..(N-1)
                          /\ ((c + (i - 1)) % N = p % N) => (i = pmc+1) 
        BY <4>2
      <4>3. (c + (i - 1)) % N \in 0..(N-1)
        <5>1. \A ppmc \in 0..(N-1): \A ii \in 1..(ppmc+1) :
                  c + (ii-1) \in Int
          BY <2>1, NAssump, SMT
        <5>2. QED
          BY <5>1, <4>1, ModN1
      <4>4. ASSUME i # pmc+1
            PROVE  (c + (i - 1)) % N # p % N
        <5>1. /\ (c + ((pmc+1) - 1)) - (c + (i - 1)) \in 0..(N-1)
              /\ (c + ((pmc+1) - 1)) - (c + (i - 1)) # 0
              /\ c + ((pmc+1) - 1) \in Int
              /\ c + (i - 1) \in Int
          <6>1. ASSUME NEW pc \in 0..N, pc # N,
                       NEW ii \in 1..(pc+1), ii # pc+1
                PROVE  /\ (c + ((pc+1)-1)) - (c + (ii - 1)) \in 0..(N-1)
                       /\ (c + ((pc+1)-1)) - (c + (ii - 1)) # 0
                       /\ c + ((pc+1)-1) \in Int
                       /\ c + (ii - 1) \in Int
            BY <2>1, <6>1, NAssump, SMT
          <6>2. QED
            BY <6>1, <4>4 DEF Inv, PCInv, Producer
        <5>2. ASSUME NEW a \in Int, NEW b \in Int,  
                     a - b \in 0..(N-1),
                     a - b # 0
              PROVE  a % N # b % N
          <6>1. ((a % N) - (b % N)) % N # 0
            <7>1. ((a % N) - (b % N)) % N = (a - b) % N
              BY <5>2, ModN3
            <7>2. @ = a - b 
              BY <5>2, ModN2
            <7>3. QED
             BY <5>2, <7>1, <7>2
          <6>2. ASSUME NEW j \in 0..(N-1), NEW k \in 0..(N-1)  
                PROVE  (j - k) % N # 0 => j # k
            <7>1. \/ /\ j - k \in 0..(N-1)
                     /\ (j-k) # 0 => j # k
                  \/ /\ j - k + N \in 0..(N-1)
                     /\ j # k
              BY NAssump, SMT
            <7>2. CASE /\ j - k \in 0..(N-1)
                       /\ (j-k) # 0 => j # k
              BY <6>2, <7>2, ModN2
            <7>3. QED
              BY <7>1, <7>2
          <6>3. QED
            BY <6>1, <6>2, <5>2, ModN1, ModN2
        <5>3. QED
          BY <5>1, <5>2, <4>2
      <4>5. QED
        BY <4>3, <4>4
    <3>5. chBar' = [i \in 1..((p (-) c) + 1) |-> 
                      IF (c + i - 1) % N = p % N THEN v 
                                                 ELSE buf[(c + i - 1) % N]]
      BY <3>1, <3>4, ProduceConsume DEF Inv, TypeOK, chBar, Producer
    <3>6. ASSUME NEW i \in 1..((p(-)c)+1), i # (p(-)c)+1 
          PROVE  chBar[i] = buf[(c+i-1)%N]
      <4>1. \A pmc \in 0..N :
                i \in 1..(pmc+1) /\ i # pmc+1 => i \in 1..pmc
         BY NAssump, SMT
      <4>2. i \in 1..(p (-) c)
        BY <4>1, <3>6 DEF Inv, PCInv
      <4>3. QED
        BY <4>2 DEF chBar
    <3>7. <3>3!2 = <3>5!2
      BY <3>4, <3>6 DEF chBar
    <3>8. QED
      BY <3>3, <3>5, <3>7
  <2>5. ASSUME Inv, Consumer
        PROVE  C!Rcv
    <3> USE Consumer
    <3> SUFFICES chBar' = Tail(chBar) 
      BY <2>3, ProduceConsume DEF Consumer, C!Rcv
    <3> DEFINE pmc == p (-) c
    <3>1. Tail(chBar) = [i \in 1..(pmc-1) |-> chBar[i+1]]
      BY <2>3, ProduceConsume, TailDef
    <3>2. \A i \in 1..(pmc-1) : chBar[i+1] = buf[(c + i) % N]
      <4> SUFFICES ASSUME NEW i \in 1..(pmc-1)
                   PROVE  chBar[i+1] = buf[(c + i) % N]
        OBVIOUS
      <4>1. \A pc \in 0..N : 
              \A ii \in 1..(pc-1) :
                pc # 0 => /\ ii+1 \in 1..pc
                          /\ (c + (ii+1) - 1) = c + ii
        BY <2>1, NAssump, SMT
      <4>2. /\ i + 1 \in 1..pmc
            /\ (c + (i+1) - 1) = c + i
        BY <4>1, ProduceConsume DEF Inv, PCInv
      <4>3. QED
        BY <4>2 DEF chBar
    <3>3. Tail(chBar) = [i \in 1..(pmc-1) |-> buf[(c + i) % N]]
      BY <3>1, <3>2
    <3>4. /\ pmc' = pmc-1
          /\ \A i \in 1..(pmc-1) : (c' + i - 1) % N = (c + i) % N
      <4>1. SUFFICES ASSUME NEW i \in 1..(pmc-1) 
                     PROVE (c' + i - 1) % N = (c + i) % N
        BY ProduceConsume
      <4>2. /\ c' \in Int
            /\ i-1 \in Int
            /\ c+1 \in Int
            /\ (c+1) + (i-1) = c + i
        <5>1. /\ c+1 \in Int
              /\ \A pc \in 0..N :
                   \A ii \in 1..(pc-1) : /\ ii-1 \in Int
                                        /\ (c+1) + (ii-1) = c + ii
          BY <2>1, NAssump, SMT
        <5>2. c' \in Int
          <6>1. K \in Nat \ {0}
            <7>1. \A k \in Int : (k > N) => (k \in Nat \ {0})
              BY NAssump, SMT
            <7>2. QED
              BY <7>1, KFacts
          <6>2. c' \in 0..(K-1)
            <7>1. (c + 1) % K \in 0..(K-1)
              BY <2>1, <5>1, <6>1, ModDef
            <7>2. QED 
              BY <7>1 DEF Consumer, (+), K
          <6>3. \A k \in Int : \A cc \in 0..(k-1) : cc \in Int
            BY SMT
          <6>4. QED
            BY <6>2, <6>3, KFacts
        <5>3. QED
          BY <5>1, <5>2 DEF Inv, PCInv
      <4>3. (c' + i - 1) % N = ((c'%N) + ((i-1)%N))%N
        BY <4>2, ModN3
      <4>4. @ = (((c+1)%N) + ((i-1)%N))%N
        BY <4>2, Mod2N DEF Consumer, (+)
      <4>5. @ = ((c+1) + (i-1))%N
        BY <4>2, ModN3
      <4>6. @ = (c + i) % N
        BY <4>2
      <4>7 QED
        BY <4>3, <4>4, <4>5, <4>6
    <3>5. Tail(chBar) = [i \in 1..pmc' |-> buf[(c'+ i - 1) % N]]
      BY <3>3, <3>4
    <3>6. QED
      BY <3>5 DEF Consumer, chBar
  <2>6. QED
    BY <2>4, <2>5 DEF Next, C!Next
<1>3. UNCHANGED <<buf, p, c>> => UNCHANGED chBar
  BY DEF chBar
<1>4. QED
  <2> HIDE DEF Inv
  <2>1. Inv /\ [Next]_<<buf, p, c>> => [C!Next]_chBar
    BY <1>2, <1>3
  <2>3. QED
    <3> SUFFICES ASSUME Init /\ [][Next]_vars
                 PROVE C!Init /\ [][C!Next]_chBar
        BY WFC DEF Spec, C!Spec, C!vars
    <3> QED
      BY <1>1, <2>1, Invariance, PTL DEF vars
    (***********************************************************************)
    (* This follows from <1>1, <2>1, Theorem Invariance, the TLA+ proof    *)
    (* rule                                                                *)
    (*                                                                     *)
    (*        I /\ [][N]_v => []P                                          *)
    (*        I => H                                                       *)
    (*        P /\ [N]_v => [M]_u                                          *)
    (*    ----------------------------                                     *)
    (*    I /\ [][N]_v => H /\ [][M]_u                                     *)
    (*                                                                     *)
    (* and the definitions of Spec and C!Spec, since C!Spec equals         *)
    (*                                                                     *)
    (*    C!Init /\ [][C!Next]_chBar                                       *)
    (***********************************************************************)
    (* I = Init
       H = C!Init
       N = Next
       M = C!Next
       v = vars
       u = C!vars
       P = Inv
      *)

THEOREM Spec => NC!Spec
<1>1. Spec => [](chBar = newChBar)
  <2>1. Inv => (chBar = newChBar)
    <3>1. SUFFICES ASSUME Inv
                   PROVE  chBar = newChBar
      OBVIOUS
    <3>2. ASSUME NEW i \in 1..(p (-) c)
                 PROVE  /\ (c + i - 1) % N = (c (+) (i - 1)) % N
                        /\ (c + i - 1) % N \in 0..(N-1)
      (*********************************************************************)
      (* Note: c + i - 1 is parsed as c + (i - 1)                          *)
      (*********************************************************************)
      <4> DEFINE pmc == p (-) c
      <4>1. /\ c \in 0..(K-1)
            /\ p \in 0..(K-1)
            /\ p (-) c \in 0..N
        BY <3>1, KBufCtr DEF Inv, TypeOK, PCInv
      <4>2. /\ \A j \in 0..(K-1) : j \in Int
            /\ \A j \in 0..N : j \in Int
        BY KFacts, NAssump, SMT
      <4>3. /\ c \in Int
            /\ p \in Int
            /\ p (-) c \in Int
        BY <4>1, <4>2
      <4>4. \A j \in Int : i \in 1..j => 
                                /\ i \in Int
                                /\ i-1 \in Int
                                /\ c + i - 1 \in Int
        BY <4>3, SMT
      <4>5. /\ i \in Int
            /\ i-1 \in Int
            /\ c + i - 1 \in Int
        BY <3>2, <4>3, <4>4
      <4>6. (c (+) (i - 1)) % N = ((c + i-1) % 2*N) % N
        BY DEF (+)
      <4>7. @ = (c + i-1) % N
        BY <4>5, Mod2N
      <4>8. (c + i - 1) % N \in 0..(N-1)
        BY <4>5, NAssump, ModDef
      <4>9. QED 
        BY <4>6, <4>7, <4>8
    <3>3. /\ chBar \in [1..(p(-)c) -> Msg]
          /\ newChBar \in [1..(p(-)c) -> Msg]
      BY <3>1, <3>2 DEF chBar, newChBar, Inv, TypeOK
    <3>4. \A i \in 1..(p (-) c) : chBar[i] = newChBar[i]
      BY <3>2 DEF chBar, newChBar 

    <3>5 QED
      <4> DEFINE pmc == 1..(p (-) c)
      <4>1. /\ chBar \in [pmc -> Msg]
            /\ newChBar \in [pmc -> Msg]
            /\ \A i \in pmc : chBar[i] = newChBar[i]
        BY <3>3, <3>4
      <4> HIDE DEF pmc
      (*********************************************************************)
      (* Isabelle should be able to prove the goal directly from <4>1, but *)
      (* it can't because of a bug in the Isabelle/TLA+ theory.  This bug  *)
      (* should be fixed in the first release that uses Isabelle 2011,     *)
      (* which we expect to be available in late summer of 2011.           *)
      (*********************************************************************)
      <4>2. /\ chBar = [i \in pmc |-> chBar[i]]
            /\ newChBar = [i \in pmc |-> newChBar[i]]
        BY <4>1
      <4>3. [i \in pmc |-> chBar[i]] = [i \in pmc |-> newChBar[i]]
        BY <4>1
      <4>4. QED
        BY <4>2, <4>3 
  <2>2. QED
    (***********************************************************************)
    (* BY <2>1, Theorem Invariance, and the temporal logic proof rule      *)
    (*                                                                     *)
    (*      P => Q                                                         *)
    (*    ----------                                                       *)
    (*    []P => []Q                                                       *)
    (***********************************************************************)
    BY <2>1, Invariance, PTL DEF Spec
<1>2. [](chBar = newChBar) => (C!Spec => NC!Spec)
  <2>1. ASSUME chBar = newChBar
        PROVE  C!Init => NC!Init
    BY <2>1 DEF C!Init, NC!Init
  <2>2. [](chBar = newChBar) => (C!Init => NC!Init)
    (***********************************************************************)
    (* By <2>1 and temporal logic axiom []P => P                           *)
    (***********************************************************************)
    BY <2>1, PTL
  <2>3. (chBar = newChBar /\ (chBar = newChBar)') => ([C!Next]_C!vars => [NC!Next]_NC!vars)
    <3> SUFFICES ASSUME chBar = newChBar /\ chBar' = newChBar',
                        [C!Next]_C!vars
                 PROVE  [NC!Next]_NC!vars
      OBVIOUS
    <3> QED
      BY DEF C!Next, C!Send, C!Rcv, C!vars, NC!Next, NC!Send, NC!Rcv, NC!vars
  <2>4. [](chBar = newChBar) => ([][C!Next]_C!vars => [][NC!Next]_NC!vars)
    (***********************************************************************)
    (* By <2>3 and the TLA+ proof rule                                     *)
    (*                                                                     *)
    (*    P /\ P' => ([N]_v => [M]_u)                                      *)
    (*    ---------------------------                                      *)
    (*    []P => ([][N]_v => [][M]_u)                                      *)
    (***********************************************************************)
    BY <2>3, PTL
  <2>5. QED
      BY <2>2, <2>3, WFNC, PTL DEF C!Spec, NC!Spec
    (***********************************************************************)
    (* BY <2>2, <2>3 DEF C!Spec, NC!Spec                                   *)
    (***********************************************************************)
    
<1>3. QED
  (*************************************************************************)
  (* BY <1>1, <1>2, ChBarImpl                                              *)
  (*************************************************************************)
  BY <1>1, <1>2, ChBarImpl
=============================================================================
\* Modification History
\* Last modified Wed Nov 15 20:43:02 EST 2023 by alex
\* Last modified Wed May 02 16:38:46 PDT 2012 by lamport
\* Created Sun Apr 17 11:55:07 PDT 2011 by lamport
