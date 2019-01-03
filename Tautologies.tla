---------------------------- MODULE Tautologies ----------------------------
VARIABLES P, Q

F1(A, B) == A => B
F2(A, B) == ~A \/ B

ValuesEquivalent == F1(P, Q) <=> F2(P, Q)

Init ==
    /\ P \in BOOLEAN
    /\ Q \in BOOLEAN
    
Next ==
    /\ P' \in BOOLEAN
    /\ Q' \in BOOLEAN
    
Spec ==
    Init /\ [][Next]_<<P, Q>>
 
=============================================================================
\* Modification History
\* Last modified Wed Jan 02 17:21:29 EET 2019 by flakas
\* Created Tue Nov 07 23:59:56 EET 2017 by flakas
