
------------------------------ MODULE GenSyncMod ------------------------------
(***************************************************************************)
(* TLA+ specification of the algorithm for synchronization modulo k.       *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS Proc, k, D
ASSUME /\ Proc # {}
       /\ k \in Nat \ {0}
	   /\ 2*D+1 < k
N == Cardinality(Proc)

Min(S) == CHOOSE s \in S : \A t \in S : s <= t
Max(S) == CHOOSE s \in S : \A t \in S : s >= t

(* process states modeled as records *)
State		== [x : Nat, force : 0 .. 2, concordant : BOOLEAN, ready : BOOLEAN, level : 0 .. 2]
MsgTuple	== [x : Nat, force : 0 .. 2, concordant : BOOLEAN, ready : BOOLEAN]

(* messages are either a natural number or None *)
None == CHOOSE x : x \notin MsgTuple
Msg == MsgTuple \cup {None}
NoMsg == CHOOSE x : x \notin Msg

(* We count rounds modulo k *)
roundsPerPhase == k

(* initial states of processes *)
Start(p) == [x |-> 0, force |-> 0, concordant |-> FALSE, ready |-> FALSE, level |-> 0]

(* message sent from p to q at round r, where st is p's state *)
Send(p,r,st,q) == [x |-> 0, force |-> 0, concordant |-> FALSE, ready |-> FALSE]

maxForce(rcvd) == LET VV == {m \in rcvd : m[2] \in MsgTuple} IN Max({m[2].force : m \in VV})

setVal(rcvd,forceLevel) == LET VV == {m \in rcvd : m[2] \in MsgTuple /\ m[2].force = maxForce(rcvd)} IN
    {m[2].x : m \in VV}

gossipConc(rcvd) == \E v \in 0 .. (k-1) : \A m \in rcvd : m[2] \in MsgTuple /\ m[2].x % k = v /\ m[2].concordant
gossipReady(rcvd) == \A m \in rcvd : m[2] \in MsgTuple /\ m[2].concordant
readyLevel1(st,rcvd,v,conc)			== st.level = 0 /\ v % k = 0 /\ conc
readyLevel2(st,rcvd,v,conc,ready)	== st.level = 1 /\ v % k = 0 /\ conc /\ ready

(* state transition function, rcvd \in SUBSET (Proc \X (Msg \cup {NoMsg})) *)
Trans(p,r,st,rcvd) ==
	LET maxf  == maxForce(rcvd) 
	   val   == Min(setVal(rcvd,maxf)) 
		conc  == gossipConc(rcvd)
		ready == gossipReady(rcvd) IN

	LET	levelup1	== readyLevel1(st,rcvd,val,conc)
		levelup2	== readyLevel2(st,rcvd,val,conc,ready) IN

	LET level == IF levelup1 THEN 1 ELSE IF levelup2 THEN 2 ELSE st.level IN

	[x |-> val,
	 force |-> maxf,
	 concordant |-> conc,
	 ready |-> IF val = 0 /\ level > 0 THEN TRUE ELSE ready,
	 level |-> level]

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
	/\ \A u \in Proc : u \in HO[u]
	/\	\A u \in Proc : \E path \in [0 .. (D-2) -> Proc] :
	   /\ \A i \in 0 .. (D-3) : path[i] \in HO[path[i+1]]
	   /\ u = path[0]
	   /\  path[D-2] = centralProc
	/\ Step(HO)

CentralSpec == Init /\ [][CentralNext]_vars

-----------------------------------------------------------------------------

Safety == 
  \E c \in 0 .. (k-1) : \A p \in Proc \ asleep : (state[p].level = 2 /\ state[p] % k = 0) => round = c

Liveness ==
	\A p \in Proc : <> (state[p].level = 2)

=============================================================================
\* Modification History
\* Last modified Thu Dec 17 13:03:09 CET 2020 by louis
\* Last modified Fri Dec 11 11:42:02 CET 2020 by merz
\* Created Thu Dec 10 17:55:14 CET 2020 by merz
