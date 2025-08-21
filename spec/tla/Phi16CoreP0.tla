---- MODULE Phi16CoreP0 ----
EXTENDS Naturals, TLC

CONSTANTS N, EPS

VARIABLES state, data, prevData

vars == <<state, data, prevData>>

Init ==
    /\ state = "HOLD"
    /\ data = [i \in 0..N-1 |-> 0]
    /\ prevData = data

Run ==
    /\ state = "RUN"
    /\ state' = "RUN"
    /\ data' = [i \in 0..N-1 |-> data[i]]
    /\ prevData' = data

Hold ==
    /\ state = "HOLD"
    /\ state' \in {"HOLD", "RUN"}
    /\ UNCHANGED data
    /\ prevData' = data

Next == Run \/ Hold

Spec == Init /\ [][Next]_vars

INV_TypeOK ==
    /\ state \in {"RUN", "HOLD"}
    /\ data \in [0..N-1 -> {0,1}]
    /\ prevData \in [0..N-1 -> {0,1}]

NoWriteInHold == [] (state = "HOLD" => data = prevData)

NoWriteInHoldStruct == state = "HOLD" => data = prevData

====
