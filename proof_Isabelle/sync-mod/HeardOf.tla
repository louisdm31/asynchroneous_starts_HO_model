------------------- MODULE HeardOf ----------------------------
(*
  Coarse-grained executions of Heard-of model. The idea is that
  all processes advance their round (and emit the corresponding
  messages) simultaneously. The message history is not preserved
  so that the model becomes finite-state (provided the
  underlying state space is finite). Round numbers are counted
  modulo the parameter roundsPerPhase, the idea being that a
  phase consists of a fixed number of rounds.
  While processes are modeled as executing synchronously, they
  need not start simultaneously but may be inactive ("asleep")
  initially.
*)
EXTENDS Naturals
CONSTANTS 
  Proc,           (* set of processes *)
  State,          (* set of possible process states *)
  Msg,            (* set of messages used by this algorithm *)
  NoMsg,          (* default message value indicating that the sender is sleeping *)
  roundsPerPhase, (* number of rounds that make up a phase *)
  Start(_),       (* Start(p): initial state of process p *)
  Send(_,_,_,_),  (* Send(p,r,st,q): message sent from p to q at beginning of                            round r given process state st of p *)
  Trans(_,_,_,_)  (* Trans(p,r,st,rcvd): state transition function *)

Round == 0 .. roundsPerPhase-1

ASSUME
  /\ roundsPerPhase >= 1
  /\ NoMsg \notin Msg
  /\ \A p \in Proc : Start(p) \in State
  /\ \A p,q \in Proc, st \in State, r \in Round : Send(p,r,st,q) \in Msg
  /\ \A p \in Proc, rd \in Round, st \in State, rcvd \in SUBSET (Proc \X Msg) :
          Trans(p,rd,st,rcvd) \in State

VARIABLES
  round,   (* current round (modulo roundsPerPhase) *)
  asleep,  (* set of sleeping processes *)
  state,   (* state[p] : local state of process p *)
  heardof  (* headof[p] : process p's heard-of set *)
(* Variable heardof is used only for debugging: it records the
   HO set of the preceding round. To reduce the number of states
   inspected by TLC, it should not be part of the VIEW -- cf.
   definition of noHeardofView below. *)

-------------------------------------------------------------

TypeInv ==
  /\ round \in Round
  /\ asleep \in SUBSET Proc
  /\ state \in [Proc -> State]
  /\ heardof \in [Proc -> SUBSET Proc]
 
Init ==
  /\ round = 0
  /\ asleep \in SUBSET Proc
  /\ state = [p \in Proc |-> Start(p)]
  /\ heardof = [p \in Proc |-> {}]   (* arbitrary *)

(* The step action receives and processes the messages of the current
   round, based on an assignment of heard-of sets, and sends the
   messages for the following round. *)
Step(HO) == 
  LET rcvd(p) == { << q, IF q \in asleep THEN NoMsg
                         ELSE Send(q, round, state[q], p) >> : q \in HO[p] }
  IN  /\ round' = (round + 1) % roundsPerPhase
      /\ asleep' \in SUBSET asleep
      /\ state'   = [p \in Proc |-> IF p \in asleep THEN state[p]
                                    ELSE Trans(p,round,state[p],rcvd(p))]
      /\ heardof' = HO

Next == 
  \E HO \in [Proc -> SUBSET Proc] : Step(HO)

(* The following variant requires that each process receives its
   own message. Looks innocent but doesn't work well, for example,
   with uniform rounds. *)
NextHearSelf == 
  \E HO \in [Proc -> SUBSET Proc] : 
     /\ \A p \in Proc: p \in HO[p]
     /\ Step(HO)

NoSplitHeardOf(HO) ==  (* HO sets satisfying no-split condition *)
  \A p,q \in Proc : HO[p] \cap HO[q] # {}

NextNoSplit ==
  \E HO \in [Proc -> SUBSET Proc] : 
     /\ NoSplitHeardOf(HO)
     /\ Step(HO)

Uniform(HO) == \E S \in SUBSET Proc:
  /\ S # {}
  /\ HO = [p \in Proc |-> S]

NextUniform == \E S \in SUBSET Proc :
     /\ S # {}
     /\ Step([p \in Proc |-> S])

vars == <<round, asleep, state, heardof>>

noHeardofView == <<round, asleep, state>>

Spec== Init /\ [][Next]_vars

NoSplitSpec == Init /\ [][NextNoSplit]_vars

InfinitelyUniform == WF_vars(NextUniform)

==============================================================
