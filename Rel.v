(* Chapter 7: Properties of relations *)

Require Export SfLib.

Definition relation (X:Type) := X -> X -> Prop.

(* le:  x <= y *)
Print le.
Check le : nat -> nat -> Prop.
Check le : relation nat.


(* Basic properties of relations *)
Definition partial_function {X:Type} (R:relation X) := forall x y1 y2 : X,
  R x y1 -> R x y2 -> y1 = y2.

Theorem le_not_partial_function: ~ (partial_function le).
Proof.
  unfold not, partial_function. intros.
  assert (0 = 1) as contra.
  Case "proof of contra".
    apply H with (x:=0). apply le_n. apply le_S. apply le_n.
  inversion contra.
Qed.


Definition reflexive {X:Type} (R:relation X) :=
  forall a:X, R a a.

Theorem le_reflexive: reflexive le.
Proof.
  unfold reflexive. intros.
  apply le_n.
Qed.


Definition transitive {X:Type} (R:relation X) :=
  forall a b c : X, R a b -> R b c -> R a c.

Theorem le_transitive: transitive le.
Proof.
  unfold transitive. intros. induction H0.
  Case "b<=c". apply H.
  Case "b<=S c". apply le_S. apply IHle.
Qed.


Theorem lt_trans: transitive lt.
Proof.
  unfold lt, transitive. intros a b c Hab Hbc.
  apply le_S in Hab. apply le_transitive with (a := (S a)) (b := (S b)) (c := c).
  apply Hab. apply Hbc.
Qed.

Theorem lt_trans': transitive lt.
Proof.
  unfold lt, transitive. intros a b c Hab Hbc. induction Hbc.
  Case "b<=0". apply le_S. apply Hab.
  Case "b<=S". apply le_S. apply IHHbc.
Qed.

Theorem lt_trans'': transitive lt.
Proof.
  unfold lt, transitive. intros n m o Hnm Hmo. induction o.
  Case "o=0". inversion Hmo. apply le_S. apply IHo. inversion Hmo.
Admitted.


Theorem le_Sn_le: forall n m, S n <= m -> n <= m.
Proof.
  intros. apply le_transitive with (S n).
  Case "n<=S n". apply le_S. reflexivity.
  Case "S n <= m". apply H.
Qed.

(* Exercise: * *)
Theorem le_S_n: forall n m,
  (S n <= S m) -> (n <= m).
Proof.
  intros. inversion H. reflexivity.
  apply le_Sn_le. apply H1.
Qed.

(* Exercise: * *)
Theorem le_Sn_n: forall n,
  ~ (S n <= n).
Proof.
  unfold not. intros.
  apply le_Sn_n in H. apply H.
Qed.

Definition symmetric {X:Type} (R:relation X) :=
  forall a b : X, R a b -> R b a.

(* Exercise: ** *)
Theorem le_not_symmetric: ~ (symmetric le).
Proof.
  unfold not, symmetric.
  intros. assert (1 <= 0) as contra.
  Case "proof of assert".
    apply H with (b:=1). apply H. apply H. apply le_S. reflexivity.
  inversion contra.
Qed.

Definition antisymmetric {X:Type} (R:relation X) := forall a b : X,
  R a b -> R b a -> a = b.

(* Exercise: ** *)
Theorem le_antisymmetric: antisymmetric le.
Proof.
  unfold antisymmetric. intros a b Hab Hba.
Admitted.


(* Exercise: ** *)
Theorem le_step: forall n m p,
  n < m -> m <= S p -> n <= p.
Proof.
  intros. apply le_transitive with n.
  Case "n<=n". reflexivity.
  Case "n<=Sn". unfold "<" in H. rewrite H0 in H. apply le_S_n. apply H.
Qed.

Definition preorder {X:Type} (R:relation X) :=
  (reflexive R) /\ (transitive R).

Definition equivalence {X:Type} (R:relation X) :=
  (preorder R) /\ (symmetric R).

(* Really a partial order. Coq stdlib calls it order *)
Definition order {X:Type} (R:relation X) :=
  (preorder R) /\ (antisymmetric R).

Theorem le_order: order le.
Proof.
  unfold order, preorder. split. split.
  Case "refl". apply le_reflexive.
  Case "trans". apply le_transitive.
  Case "antisymmetric". apply le_antisymmetric.
Qed.



(* Reflexive, transitive closure *)
Inductive clos_refl_trans {A:Type} (R:relation A) : relation A :=
  | rt_step  : forall x y, R x y -> clos_refl_trans R x y
  | rt_refl  : forall x, clos_refl_trans R x x
  | rt_trans : forall x y z, clos_refl_trans R x y ->
                             clos_refl_trans R y z ->
                             clos_refl_trans R x z.

Theorem next_nat_closure_is_le : forall n m,
  n <= m <-> ((clos_refl_trans next_nat) n m).
Proof.
  intros n m. split.
  Case "->".
    intro H. induction H.
    SCase "le_n". apply rt_refl.
    SCase "le_S". apply rt_trans with m. apply IHle. apply rt_step. apply nn.
  Case "<-".
    intro H. induction H.
    SCase "rt_step". inversion H. apply le_S. apply le_n.
    SCase "rt_refl". apply le_n.
    SCase "rt_trans".
      apply le_transitive with y. apply IHclos_refl_trans1. apply IHclos_refl_trans2.
Qed.



(* more useful definition of reflexive, transitive closure *)
Inductive refl_step_closure {X:Type} (R:relation X) : relation X :=
| rsc_refl : forall x:X, refl_step_closure R x x
| rsc_step : forall x y z : X, R x y ->
                               refl_step_closure R y z ->
                               refl_step_closure R x z.


Tactic Notation "rt_cases" tactic(first) ident(c) :=
  first; [
    Case_aux c "rt_step"
  | Case_aux c "rt_refl"
  | Case_aux c "rt_trans"
  ].

Tactic Notation "rsc_cases" tactic(first) ident(c) :=
  first; [
    Case_aux c "rsc_refl"
  | Case_aux c "rsc_step"
  ].


(* Need to check that the 2 definitions of reflexive, transitive closure are the
   same
*)
Theorem rsc_R: forall (X:Type) (R:relation X) (x y : X),
  R x y -> refl_step_closure R x y.
Proof.
  intros.
  apply rsc_step with y. apply H. apply rsc_refl.
Qed.


(* Exercise: ** *)
Theorem rsc_trans : forall (X:Type) (R:relation X) (x y z : X),
  refl_step_closure R x y ->
  refl_step_closure R y z ->
  refl_step_closure R x z.
Proof.
  intros. induction H.
  Case "refl". apply H0.
  Case "step". apply IHrefl_step_closure in H0.
Admitted.


(* Exercise: *** *)
Theorem rtc_rsc_coincide: forall (X:Type) (R:relation X) (x y : X),
  clos_refl_trans R x y <-> refl_step_closure R x y.
Proof.
  unfold iff. split. intros.
  Case "->".
Admitted.