------------------------------ MODULE Phi16 ------------------------------
EXTENDS Naturals, Sequences, FiniteSets
(*************************************************************************)
(* Φ-16 — Minimal TLC-friendly skeleton                                  *)
(* Captures: R-invariant via append-only ledger, AND-level 0+,           *)
(* 3⊥+1 as append, Silence-Hold + Recover.                               *)
(*************************************************************************)
CONSTANTS
    N,                        \* number of core units (e.g., 16)
    EPS,                      \* integer epsilon (0 ⇒ unanimity; 1 ⇒ allow one drop)
    EventsSet,                \* finite set of possible events (e1, e2, ...)
    Tau                       \* allowed drop in DIA before triggering SAFE

VARIABLES
    L,        \* ledger: a sequence over EventsSet
    OK,       \* OK vector: [1..N -> {0,1}]
    Mode,     \* "RUN", "HOLD" or "SAFE"
    EvQueue   \* queue of proposed events (Seq(EventsSet))

vars == <<L, OK, Mode, EvQueue>>

IsRun  == Mode = "RUN"
IsHold == Mode = "HOLD"
IsSafe == Mode = "SAFE"

AND0plus ==
    LET S == {i \in 1..N : OK[i] = 1} IN Cardinality(S) >= (N - EPS)

DIA(seq) == Len(seq)

DIAGuard(e) == DIA(Append(L, e)) >= DIA(L) - Tau

AppendEvent(e) == L' = Append(L, e)
Init ==
    /\ L = << >>
    /\ OK \in [1..N -> {0,1}]
    /\ Mode = "RUN"
    /\ EvQueue = << >>
Propose ==
    /\ IsRun
    /\ Len(EvQueue) = 0
    /\ \E e \in EventsSet: EvQueue' = <<e>>
    /\ UNCHANGED << L, OK, Mode >>

Validate ==
    /\ IsRun
    /\ Len(EvQueue) > 0
    /\ AND0plus
    /\ DIAGuard(Head(EvQueue))
    /\ AppendEvent(Head(EvQueue))
    /\ EvQueue' = Tail(EvQueue)
    /\ UNCHANGED << OK, Mode >>

EnterHold ==
    /\ IsRun
    /\ Len(EvQueue) > 0
    /\ ~AND0plus
    /\ Mode' = "HOLD"
    /\ UNCHANGED << L, OK, EvQueue >>

EnterSafe ==
    /\ IsRun
    /\ Len(EvQueue) > 0
    /\ AND0plus
    /\ ~DIAGuard(Head(EvQueue))
    /\ Mode' = "SAFE"
    /\ UNCHANGED << L, OK, EvQueue >>

Recover ==
    /\ (IsHold \/ IsSafe)
    /\ AND0plus
    /\ (DIAGuard(Head(EvQueue)) \/ Len(EvQueue)=0)
    /\ Mode' = "RUN"
    /\ UNCHANGED << L, OK, EvQueue >>

TweakOK ==
    /\ OK' \in [1..N -> {0,1}]
    /\ UNCHANGED << L, Mode, EvQueue >>

AppendOnly == Len(L') >= Len(L)
AppendOnlyProp == [] [AppendOnly]_vars

NoAppendIfDIAFalls == (L' = L) \/ (DIA(L') >= DIA(L) - Tau)
NoAppendIfDIAFallsProp == [] [NoAppendIfDIAFalls]_vars

NoWriteInHoldSafe == (Mode \in {"HOLD", "SAFE"}) => L' = L
NoWriteInHoldSafeProp == [] [NoWriteInHoldSafe]_vars

TypeOK ==
    /\ L \in Seq(EventsSet)
    /\ OK \in [1..N -> {0,1}]
    /\ Mode \in {"RUN", "HOLD", "SAFE"}
    /\ EvQueue \in Seq(EventsSet)

Next == Propose \/ Validate \/ EnterHold \/ EnterSafe \/ Recover \/ TweakOK

Spec == Init /\ [][Next]_vars
=============================================================================
