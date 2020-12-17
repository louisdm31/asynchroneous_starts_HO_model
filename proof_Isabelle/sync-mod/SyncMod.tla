------------------------------ MODULE SyncMod ------------------------------
(***************************************************************************)
(* TLA+ specification of the algorithm for synchronization modulo k.       *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS Proc, k
ASSUME /\ Proc # {}
       /\ k \in Nat \ {0}
N == Cardinality(Proc)

Min(S) == CHOOSE s \in S : \A t \in S : s <= t

(* process states modeled as records *)
State == [x : Nat, force : BOOLEAN, fire : BOOLEAN]

(* messages are either a natural number or None *)
None == CHOOSE x : x \notin Nat
Msg == Nat \cup {None}
NoMsg == CHOOSE x : x \notin Msg

(* We count rounds modulo k *)
roundsPerPhase == k

(* initial states of processes *)
Start(p) == [x |-> k, force |-> FALSE, fire |-> FALSE]

(* message sent from p to q at round r, where st is p's state *)
Send(p,r,st,q) == IF st.x = k THEN None ELSE st.x  \* could be simplified to st.x ??

(* state transition function, rcvd \in SUBSET (Proc \X (Msg \cup {NoMsg})) *)
ReadyFire(rcvd) == \A x \in rcvd : x[2] = k-1
ReadyForce(st,rcvd) ==
  /\ ~ st.force
  /\ \A x \in rcvd : x[2] # k-1
  /\ \E x,y \in rcvd : x[1] # y[1] /\ x[2] \in Nat /\ y[2] \in Nat \ {x[2]}
Trans(p,r,st,rcvd) ==
  LET rdyForce == ReadyForce(st,rcvd)
      valsRcvd == {x[2] : x \in rcvd} \ {None, NoMsg}
  IN  [fire |-> ReadyFire(rcvd),  \* NB: unlike the Isabelle model, doesn't stay true once it's true
       force |-> IF rdyForce THEN TRUE ELSE st.force,
       x |-> IF rdyForce THEN k-1
             ELSE IF \A x \in rcvd : x[2] \in {None,NoMsg} THEN 0
             ELSE Min({(v+1) % k : v \in valsRcvd})
      ]

-----------------------------------------------------------------------------

VARIABLES round, asleep, state, heardof
INSTANCE HeardOf

(***************************************************************************)
(* The algorithm assumes that there exists some process that is always     *)
(* in the Heard-Of set of all processes. In order to break symmetry,       *)
(* we fix that process statically.                                         *)
(***************************************************************************)
centralProc == CHOOSE p \in Proc : TRUE

CentralNext == \E HO \in [Proc -> SUBSET Proc] :
  /\ \A p \in Proc : centralProc \in HO[p]
  /\ Step(HO)

CentralSpec == Init /\ [][CentralNext]_vars

-----------------------------------------------------------------------------

Safety == 
  \E c \in 0 .. (k-1) : \A p \in Proc \ asleep : state[p].fire => round = c

=============================================================================
\* Modification History
\* Last modified Thu Dec 17 12:07:59 CET 2020 by louis
\* Last modified Fri Dec 11 11:42:02 CET 2020 by merz
\* Created Thu Dec 10 17:55:14 CET 2020 by merz
