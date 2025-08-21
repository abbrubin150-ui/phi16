---- MODULE Phi16Handshake_DIA ----
EXTENDS Naturals, Sequences, TLC

(*********************************************************************)
(* Handshake + Append-only ledger + DIA monotonicity                 *)
(*********************************************************************)

CONSTANTS N, EPS, EventsSet, DIA_MAX, Tau

VARIABLES state, ok, stage, L, prop, dia
vars == <<state, ok, stage, L, prop, dia>>

TypeOK ==
  /\ state \in {"RUN","HOLD"}
  /\ ok \in [1..N -> BOOLEAN]
  /\ stage \in {"IDLE","PROPOSED","VALIDATED"}
  /\ L \in Seq(EventsSet)
  /\ prop \in (EventsSet \cup {None})
  /\ dia \in 0..DIA_MAX

SumOK == Cardinality({i \in 1..N : ok[i]})
AND0plus == SumOK >= N - EPS

(* Abstract DIA guard: the next dia on append must not drop below dia - Tau *)
DIAGuard(dOld, dNew) == dNew >= dOld - Tau

Init ==
  /\ state = "RUN"
  /\ ok \in [1..N -> BOOLEAN]
  /\ stage = "IDLE"
  /\ L = << >>
  /\ prop = None
  /\ dia = 0

Propose ==
  /\ state = "RUN"
  /\ stage = "IDLE"
  /\ \E e \in EventsSet:
        /\ stage' = "PROPOSED"
        /\ prop' = e
  /\ UNCHANGED << state, ok, L, dia >>

Validate ==
  /\ state = "RUN"
  /\ stage = "PROPOSED"
  /\ AND0plus
  /\ stage' = "VALIDATED"
  /\ UNCHANGED << state, ok, L, prop, dia >>

AppendMerge ==
  /\ state = "RUN"
  /\ stage = "VALIDATED"
  /\ \E dNew \in 0..DIA_MAX:
        /\ DIAGuard(dia, dNew)
        /\ dia' = dNew
  /\ L' = Append(L, prop)
  /\ stage' = "IDLE"
  /\ prop' = None
  /\ UNCHANGED << state, ok >>

EnterHold ==
  /\ state = "RUN"
  /\ ~AND0plus
  /\ state' = "HOLD"
  /\ stage' = "IDLE"
  /\ prop' = None
  /\ UNCHANGED << ok, L, dia >>

StayHold ==
  /\ state = "HOLD"
  /\ ~AND0plus
  /\ UNCHANGED vars

Recover ==
  /\ state = "HOLD"
  /\ AND0plus
  /\ state' = "RUN"
  /\ UNCHANGED << ok, stage, L, prop, dia >>

FlipDown ==
  /\ \E i \in 1..N : ok[i] = TRUE
  /\ \E i \in 1..N :
        /\ ok[i] = TRUE
        /\ ok' = [ok EXCEPT ![i] = FALSE]
  /\ UNCHANGED << state, stage, L, prop, dia >>

FlipUp ==
  /\ \E i \in 1..N : ok[i] = FALSE
  /\ \E i \in 1..N :
        /\ ok[i] = FALSE
        /\ ok' = [ok EXCEPT ![i] = TRUE]
  /\ UNCHANGED << state, stage, L, prop, dia >>

Next == Propose \/ Validate \/ AppendMerge \/
        EnterHold \/ StayHold \/ Recover \/
        FlipDown \/ FlipUp

Spec == Init /\ [] [Next]_vars

(*********************************************************************)
(* Properties                                                        *)
(*********************************************************************)

INV_TypeOK == TypeOK

AppendOnlyMonotone == [] [ Len(L') >= Len(L) ]_vars

NoWriteInHold == [] ( state = "HOLD" => [UNCHANGED L]_vars )

DIAMonotone == [] [ dia' >= dia ]_vars

=============================================================================
