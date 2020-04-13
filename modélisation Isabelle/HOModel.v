Require Import Ensembles.
Require Import List.
Require Import ListSet.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Classical.
Require Import Bool.
Require Import Classical.

Parameter msg proc pst: Type.
Parameter undefined : proc.
Axiom proc_dec : forall x y:proc, {x = y} + {x <> y}.

Inductive message : Type :=
  | Content : msg -> message
  | Void : message
  | Bot : message.

Inductive proc_state : Type :=
  | Active : pst -> proc_state
  | Aslept : proc_state.

Record CHOAlgorith := {
  Proc_set : set proc;
  CinitState : proc -> pst -> proc -> bool;
  SendMsg : proc -> proc -> pst -> msg;
  CnextState : proc -> pst -> (proc -> message) -> proc -> pst -> bool }.

Definition initState alg p st : bool := CinitState alg p st undefined.
Definition nextState alg p st msgs st' := CnextState alg p st msgs undefined st'.

Definition HO := proc -> Ensemble proc.
Definition coord := proc -> proc.

Definition SHOmsgVectors A p cfg HOp SHOp :=
  { mu : proc -> message | (forall q, set_In q HOp <-> mu q <> Void) /\
      forall q, set_In q (set_inter proc_dec HOp SHOp) -> match cfg q with
  | Active s => mu q = Content (SendMsg A q p s)
  | _ => mu q = Bot end}.

Definition forall_proc (A:CHOAlgorith) (f:proc -> bool) : bool :=
  let fix forall_proc_ (l:set proc) f  := match l with
  | nil => true
  | cons a ar => andb (f a) (forall_proc_ ar f) end in forall_proc_ (Proc_set A) f. 

Definition CSHOnextConfig A cfg HO SHO coord cfg' : bool :=
   forall_proc A (fun p => match cfg p with
  | Active s => match cfg' p with
    | Active s' => exists mu : (SHOmsgVectors A p cfg (HO p) (SHO p)),
           CnextState A p s (proj1_sig mu) (coord p) s' = true
    | _ => False end
  | _ => True end).

Definition CHOinitConfig A rho coord :=
  forall_proc A (fun p => (exists n : nat, (forall m, m < n -> rho m p = Aslept) /\
  match rho n p with 
  |Active s => CinitState A p s (coord n p) = true
  | _ => False end)).

Definition CSHORun A rho HOs SHOs coords :=
  CHOinitConfig A rho coords
   /\ (forall r, CSHOnextConfig A (rho r) (HOs r) (SHOs r) (coords (S r)) (rho (S r))).

Definition HOinitConfig  A cfg := CHOinitConfig A cfg (fun _ _ => undefined).

Lemma HOinitConfig_eq : forall A cfg, HOinitConfig A cfg =
  forall_proc A (fun p => exists n:nat, (forall m, m < n -> cfg m p = Aslept) /\
  match cfg n p with 
  |Active s => initState A p s = true
  | _ => False end).
trivial.
Qed.

Definition SHOnextConfig A cfg HO SHO cfg' :=
  CSHOnextConfig A cfg HO SHO (fun _ => undefined) cfg'.

Lemma SHOnextConfig_eq : forall A (cfg:proc->proc_state) HO SHO cfg',
  SHOnextConfig A cfg HO SHO cfg' = 
    forall p,  match cfg p with
  | Active s => match cfg' p with
    | Active s' => exists mu : SHOmsgVectors A p cfg (HO p) (SHO p),
        nextState A p s (proj1_sig mu) s' = true
    | _ => False end
  | _ => True end.
trivial.
Qed.

Definition SHORun A rho HOs SHOs := CSHORun A rho HOs SHOs (fun _ _ => undefined).

Lemma SHORun_eq : forall A rho HOs SHOs, SHORun A rho HOs SHOs =
  (HOinitConfig A rho /\ (forall r, SHOnextConfig A (rho r) (HOs r) (SHOs r) (rho (S r)))).
trivial.
Qed.

Definition HOrcvMsgs A p (HO:set proc) cfg := fun q : proc =>
  match set_In_dec proc_dec q HO with
  | left _ => 
    match cfg q with
    | Active s =>  Content (SendMsg A q p s)
    | Aslept => Bot end
  | right _ => Void end.

Lemma SHOmsgVectors_HO : forall A p cfg HO,
  forall mu : SHOmsgVectors A p cfg HO HO, proj1_sig mu = HOrcvMsgs A p HO cfg.
intros.
apply functional_extensionality.
intro.
induction mu.
unfold proj1_sig.
unfold HOrcvMsgs.
case (set_In_dec proc_dec x HO0); intro.
assert (s2:=s).
apply p0 in s.
assert (s3 := (proj2 p0)  x (set_inter_intro proc_dec x HO0 HO0 s2 s2)).

destruct (cfg x).
assumption.
assumption.

assert (H:=proj1 p0 x).
apply not_iff_compat in H.
apply H in n.
apply NNPP in n.
trivial.
Qed.

Definition CHOnextConfig A cfg HO coord cfg' :=
   CSHOnextConfig A cfg HO HO coord cfg'.

Lemma CHOnextConfig_eq : forall A cfg HO coord cfg',
  CHOnextConfig A cfg HO coord cfg' =
  forall p,  match cfg p with
  | Active s => match cfg' p with
    | Active s' => CnextState A p s (HOrcvMsgs A p (HO p) cfg) (coord p) s' = true
    | _ => False end
  | _ => True end.
intros.
unfold CHOnextConfig.
unfold CSHOnextConfig.
apply forall_extensionalityP.
intro.
case (cfg x).
intro.
case (cfg' x).
intro.

induction (CnextState A x p (HOrcvMsgs A x (HO0 x) cfg) (coord0 x) p0).

assert(H:=classic (exists mu : SHOmsgVectors A x cfg (HO0 x) (HO0 x),
   CnextState A x p (proj1_sig mu) (coord0 x) p0 = true)).
destruct H.
destruct H.

exists (HOrcvMsgs A x (HO0 x) cfg).
unfold HOrcvMsgs.
rewrite <- (SHOmsgVectors_HO.
trivial.
