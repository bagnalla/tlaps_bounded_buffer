# TLAPS Bounded Buffer Proof

This is an fixed/updated version of the bounded buffer TLAPS proof originally written by Leslie Lamport and described in chapter 13 of the TLA+ hyperbook. The original version seems to have been written before the PTL (propositional temporal logic) backend was added to TLAPS, so proof steps that required temporal reasoning were omitted. This version fills in those steps so they can be successfully proved by the current PTL backend (ls4). The informal proofs of those steps described in Lamport's comments were actually not quite right; the necessary corrections are described below. 

## Proofs no longer omitted

- A couple cases of Lemma `ModDef`.
- Lemmas `SeqDef` and `EmptySeq`. `AppendDef` and `TailDef` are still omitted.
- Theorem `ChBarImpl == Spec => C!Spec` - the main theorem proving that the bounded buffer algorithm implements the bounded channel specification under refinement mapping `C`.
- Theorem `Spec => NC!Spec` - alternate form of the main theorem wrt. refinement mapping `NC`.

## Weak fairness of the consumer/receiver

The original proof seems to have not taken fairness into account at all, despite the spec requiring weak fairness of the consumer/receiver. Probably the proof was written for a previous version of the spec that didn't require fairness and was not updated when the spec was changed to require it (and this was not caught because the temporal reasoning steps affected by the change were not being machine-checked). Proving fairness seems to be a bit complicated (see Section 8.3.3 of the TLA+ hyperbook), thus we have the following new omitted theorems:

- `WFC` - weak fairness of the bounded buffer consumer implies weak fairness of the bounded channel receiver under refinement mapping `C`.
- `WFNC` - weak fairness of the bounded channel receiver under refinement mapping `C` implies weak fairness of the bounded channel receiver under refinement mapping `NC`.

Also, the statement of Theorem `Invariance` has been changed from `Spec => []Inv` to `Init /\ [][Next]_vars => []Inv`. The two statements are equivalent when weak fairness is not required for the consumer (because then `Spec == Init /\ [][Next]_vars`), but not when fairness is required because then `Spec == Init /\ [][Next]_vars /\ WF_vars(Consumer)`.
