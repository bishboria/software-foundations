(* Chapter 12 More on Induction *)

Require Export "ProofObjects".


(* Induction principles *)
Check nat_ind.
(*
   nat_ind : forall P : nat -> Prop,
     P 0 ->
     (forall n : nat, P n -> P (S n)) ->
     forall n : nat, P n
*)

Theorem mult_0_r': forall n:nat,
  n * 0 = 0.
Proof.
  apply nat_ind.
  Case "0".
    reflexivity.
  Case "S".
    simpl. intros. apply H.
Qed.

(* Exercise: ** optional *)
Theorem plus_one_r': forall n:nat,
  n + 1 = S n.
Proof.
  apply nat_ind.
  Case "0".
    reflexivity.
  Case "S".
    simpl. intros. apply f_equal. apply H.
Qed.


Inductive yesno : Type :=
| yes : yesno
| no  : yesno.

Check yesno_ind.
(* yesno_ind
     : forall P : yesno -> Prop, P yes -> P no -> forall y : yesno, P y
*)


(* Exercise: * *)
Inductive rgb : Type :=
| red : rgb
| green : rgb
| blue : rgb.
(*
   rgb_ind : forall P : rgb -> Prop,
   P red ->
   P green ->
   P blue ->
   forall r : rgb, P r
*)
Check rgb_ind.

Inductive natlist : Type :=
| nnil  : natlist
| ncons : nat -> natlist -> natlist.

Check natlist_ind.
(*
   natlist : forall P : natlist -> Prop,
     P nnil ->
     (forall (n:nat) (l:natlist), P l -> P (ncons n l)) ->
     forall l:natlist, P l
*)


(* Exercise: * optional *)
Inductive natlist1 : Type :=
| nnil1 : natlist1
| nsconc1 : natlist1 -> nat -> natlist1.
(*
   natlist1_ind: forall P : natlist1 -> Prop,
     P nnil1 ->
     (forall (l:natlist1) (n:nat), P l -> P (nsconc1 l n)) ->
     forall l:natlist1, P l
*)
Check natlist1_ind.


(* Exercise: * optional *)
Inductive byntree : Type :=
| bempty : byntree
| bleaf  : yesno -> byntree
| nbranch : yesno -> byntree -> byntree -> byntree.

(*
   byntree_ind: forall P : byntree -> Prop,
     P bempty ->
     (forall y:yesno, P (bleaf y)) ->
     (forall (y:yesno) (t1 t2 : byntree), P t1 -> P t2 -> P (nbranch y t1 t2)) ->
     forall b:byntree, P b
*)
Check byntree_ind.


(* Exercise: * optional *)
(* Given:
    ExSet_ind :
           ∀P : ExSet → Prop,
               (∀b : bool, P (con1 b)) →
               (∀(n : nat) (e : ExSet), P e → P (con2 n e)) →
               ∀e : ExSet, P e
*)
Inductive ExSet : Type :=
| con1 : bool -> ExSet
| con2 : nat -> ExSet -> ExSet.
Check ExSet_ind.

Inductive list (X:Type) : Type :=
| nil : list X
| cons : X -> list X -> list X.
(*
   list_ind: forall (X:Type) (P : list X -> Prop),
     P [] ->
     (forall (x:X) (l:list X), P l -> P (x :: l)) ->
     forall l:list X, P l
*)


(* Exercise: * optional *)
Inductive tree (X:Type) : Type :=
| leaf : X -> tree X
| node : tree X -> tree X -> tree X.
(*
   tree_ind : forall (X:Type) (P:tree X -> Prop),
     (forall x:X, P (leaf x)) ->
     (forall t1 t2 : tree X, P t1 -> P t2 -> P (node t1 t2)) ->
     forall t:tree X, P t
*)
Check tree_ind.

(* Exercise : * optional *)
(* Given:
   mytype_ind : forall (X:Type) (P:mytype X -> Prop),
     (forall x:X, P (constr1 X x)) ->
     (forall n:nat, P (constr2 X n)) ->
     (forall m:mytype X, P m ->
       forall n:nat, P (constr3 X m n)) ->
     forall m:mytype X, P m
*)
Inductive mytype (X:Type) : Type :=
| constr1 : X -> mytype X
| constr2 : nat -> mytype X
| constr3 : mytype X -> mytype X -> mytype X.
Check mytype_ind.


(* Exercise: * optional *)
(* Given:
   foo_ind : forall (X Y : Type) (P : foo X Y -> Prop),
     (forall x:X, P (bar X Y x)) ->
     (forall y:Y, P (baz X Y y)) ->
     (forall f1:nat -> foo X Y,
       (forall n:nat, P (f1 n)) -> P (quux X Y f1)) ->
     forall f2:foo X Y, P f2
*)
Inductive foo (X Y : Type) : Type :=
| bar : X -> foo X Y
| baz : Y -> foo X Y
| quux : (nat -> foo X Y) -> foo X Y.
Check foo_ind.


(* Exercise: * optional *)
Inductive foo' (X:Type) : Type :=
| C1 : list X -> foo' X -> foo' X
| C2 : foo' X.
(* foo'_ind: forall (X:Type) (P:foo' X -> Prop),
     (forall (l:list X) (f:foo' X), P f -> P (C1 X l f)) ->
     P (C2 X) ->
     forall f:foo' X, P f
*)
Check foo'_ind.


(* Induction hypotheses *)
Definition P_m0r (n:nat) : Prop := n * 0 = 0.

Theorem mult_0_r'' : forall n:nat,
  P_m0r n.
Proof.
  apply nat_ind.
  Case "0".
    reflexivity.
  Case "S".
    (* naming the proposition hilights the induction hypothesis *)
    intros. unfold P_m0r in *. simpl. apply H.
Qed.



(* More on the [induction] tactic *)

(* induction on a variable already in the context automatically re-generalizes
   that variable *)
Theorem plus_assoc': forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p. (* consider arbitrary n m p *)
  induction n.  (* prove for all n, and hence the particular n in the context *)
  Case "0". reflexivity.
  Case "S". (* 'n' in the context is now the n='S n' case
               left with P (S n) *)
    simpl. rewrite IHn. reflexivity.
Qed.

Theorem plus_comm': forall n m : nat,
  n + m = m + n.
Proof.
  induction n.
  Case "0". intros. rewrite plus_0_r. reflexivity.
  Case "S". intros. simpl. rewrite IHn. rewrite <- plus_n_Sm. reflexivity.
Qed.


(* induction on a variable that is quantified in the goal after some other
   quantifiers, the induction tactic will automatically introduce the variables
   bound by these quantifiers into the context *)
Theorem plus_comm'': forall n m : nat,
  n + m = m + n.
Proof.
  induction m.
  Case "0". simpl. rewrite plus_0_r. reflexivity.
  Case "S". simpl. rewrite <- plus_n_Sm. rewrite IHm. reflexivity.
Qed.


(* Exercise: * optional *)
Definition P_plus_assoc (n : nat) : Prop := forall m p, n + (m + p) = (n + m) + p.

Theorem plus_assoc: forall n, P_plus_assoc n.
Proof.
  apply nat_ind.
  Case "0". unfold P_plus_assoc. reflexivity.
  Case "S".
    unfold P_plus_assoc in *. intros. simpl. rewrite H. reflexivity.
Qed.


(* Generalizing inductions *)
Lemma one_not_beautiful_failed: ~ beautiful 1.
Proof.
  intro H.
  (* inversion H doesn't get us very far in the bsum case *)
  induction H. (* lost all information about H *)
Abort.


(*
   induction over a Prop only works properly over completely general instances
   of Prop. that is, one in which all the arguments are unconstrained variables.
*)


Lemma one_not_beautiful: forall n, n = 1 -> ~ beautiful n.
Proof.
  intros n eq h.
  induction h.
  Case "b0". inversion eq.
  Case "b3". inversion eq.
  Case "b5". inversion eq.
  Case "bsum". destruct n.
    SCase "0". destruct m.
      SSCase "0". inversion eq.
      SSCase "S". apply IHh2. apply eq.
    SCase "S". destruct m.
      SSCase "0". apply IHh1. rewrite plus_0_r in eq. apply eq.
      SSCase "S". inversion eq. rewrite <- plus_n_Sm in H0. inversion H0.
Qed.

Lemma one_not_beautiful': ~ beautiful 1.
Proof.
  intros H.
  remember 1 as n eqn:eq. (* generalized the hypothesis, added n=1 as a prop *)
  induction H. (* now as before *)
Admitted.

(* Informal proofs (advanced) *)

(* section on how to write informal proofs:
    induction over inductively defined set S: ∀ n : S, P n
      - one proof case for each constructor of S
      - if any of the constructor arguments has type S, state induction hypothesis
        for those arguments
    induction over inductively defined propostions: ∀ x y z, Q x y z -> P x y z
      - one case for each constructor of Q.
      - same idea as above
*)



(* Optional material *)
(* additional detail about how induction works in coq *)
Inductive gorgeous : nat -> Prop :=
| g0 : gorgeous 0
| g3 : forall n, gorgeous n -> gorgeous (3 + n)
| g5 : forall n, gorgeous n -> gorgeous (5 + n).
Check gorgeous_ind.

Theorem gorgeous__beautiful': forall n, gorgeous n -> beautiful n.
Proof.
  intros.
  apply gorgeous_ind.
  Case "g0". apply b0.
  Case "g3". intros. apply bsum. apply b3. apply H1.
  Case "g5". intros. apply bsum. apply b5. apply H1.
  apply H.
Qed.

(*
   the form of an inductive definition affects the induction principle that coq
   generates. the induction principle for le' is messier than le''
*)
Inductive le': nat -> nat -> Prop :=
  | le_n : forall n, le' n n
  | le_s : forall n m, le' n m -> le' n (S m).

Inductive le'' (n:nat) : nat -> Prop :=
| le_nn : le'' n n
| le_ss : forall m, le'' n m -> le'' n (S m).

Check le'_ind.
Check le''_ind.


(* induction principles for other logical propositions *)
Inductive eq' {X:Type} (x:X) : X -> Prop :=
  refl_equal' : eq' x x.
Notation "x === y" := (eq' x y) (at level 60).
Check eq'_ind.

Check and_ind.
Check or_ind.