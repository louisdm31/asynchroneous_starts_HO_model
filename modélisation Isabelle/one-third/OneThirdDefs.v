Require Import List.
Require Import Nat.
Require Import ListSet.

Parameter proc : Type.
Parameter proc_set : set proc.
Parameter n : nat.
Parameter val : Type.
Axiom val_dec : forall x y:val, {x = y} + {x <> y}.
Parameter val_ord : val -> val -> bool.

Inductive pstate : Type :=
  | Decided : val -> pstate
  | Undecided : val -> pstate. 

Inductive message : Type :=
  | Content : val -> message
  | Void : message
  | Bot : message.

Fixpoint FrequenceValRcvd msgs freq := match msgs with
  | nil => freq
  | cons (Content m) ms => fun p => match p with 
    | Content pp => match val_dec m pp with
      | left _ => S (freq (Content m)) 
      | right _ => freq p end
    | _ => freq p end
  | cons _ ms => FrequenceValRcvd ms freq end.

Fixpoint MaxFrequence msgs (freq:message -> nat) (v:message) : message := match msgs, v with
  | nil, _=> v
  | cons (Content m) ms, Content vv => MaxFrequence ms freq
      (if orb (ltb (freq v)(freq (Content m))) (andb (eqb (freq (Content m))(freq v))(val_ord m vv))
      then (Content m) else v)
  | cons (Content m) ms, _ => MaxFrequence ms freq (Content m)
  | cons _ ms, v => MaxFrequence ms freq v end.

Definition transition st msgs := let freq := FrequenceValRcvd msgs (fun p => 0) in
  let xmax := MaxFrequence msgs freq Bot in match st, xmax with
  | Decided x, _ => Decided x
  | Undecided x, Content mmax => if ltb n (freq xmax) then Decided mmax else Undecided mmax
  | Undecided x, _ => Undecided x end.
