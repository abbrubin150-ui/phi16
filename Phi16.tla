------------------------------ MODULE Phi16 ------------------------------
EXTENDS Naturals, Sequences
(*************************************************************************)
(* Φ-16 — Minimal TLC-friendly skeleton                                  *)
(* Captures: R-invariant via append-only ledger, AND-level 0+,           *)
(* 3⊥+1 as append, Silence-Hold + Recover.                               *)
(*************************************************************************)
CONSTANTS
    N,                        \* number of core units (e.g., 16)
    EPS,                      \* integer epsilon (0 ⇒ unanimity; 1 ⇒ allow one drop)
    W,                        \* weights function [1..N -> Nat], usually all 1
    EventsSet                 \* finite set of possible events (e1, e2, ...)
VARIABLES
    L,        \* ledger: a sequence over EventsSet
    OK,       \* OK vector: [1..N -> {0,1}]
    Mode,     \* "RUN" or "HOLD"
    EvQueue   \* queue of proposed events (Seq(EventsSet))
IsRun  == Mode = "RUN"
IsHold == Mode = "HOLD"
AND0plus ==
    LET S == Sum({ W[i] * OK[i] : i \in 1..N }) IN S >= (N - EPS)
DIAGuard ==
    IF Len(EvQueue) = 0 THEN FALSE
    ELSE Head(EvQueue) \in EventsSet
AppendEvent(e) == L' = Append(L, e)
Init ==
    /\ L = << >>
    /\ OK \in [1..N -> {0,1}]
    /\ Mode = "RUN"
    /\ EvQueue \in Seq(EventsSet)
Propose ==
    /\ IsRun
    /\ \E e \in EventsSet: EvQueue' = Append(EvQueue, e)
    /\ UNCHANGED << L, OK, Mode >>
ApproveAndMerge ==
    /\ IsRun
    /\ Len(EvQueue) > 0
    /\ AND0plus
    /\ DIAGuard
    /\ AppendEvent(Head(EvQueue))
    /\ EvQueue' = Tail(EvQueue)
    /\ UNCHANGED << OK, Mode >>
EnterHold ==
    /\ IsRun
    /\ Len(EvQueue) > 0
    /\ ~AND0plus \/ ~DIAGuard
    /\ Mode' = "HOLD"
    /\ UNCHANGED << L, OK, EvQueue >>
Recover ==
    /\ IsHold
    /\ AND0plus
    /\ (DIAGuard \/ Len(EvQueue)=0)
    /\ Mode' = "RUN"
    /\ UNCHANGED << L, OK, EvQueue >>
TweakOK ==
    /\ OK' \in [1..N -> {0,1}]
    /\ UNCHANGED << L, Mode, EvQueue >>
Next == Propose \/ ApproveAndMerge \/ EnterHold \/ Recover \/ TweakOK
Spec == Init /\ [][Next]_<<L,OK,Mode,EvQueue>>
=============================================================================
