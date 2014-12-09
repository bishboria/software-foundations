(* Chapter 6 Logic *)

Require Export MoreCoq.
Require Import Basics.

(* Propositions *)
Check 3 = 3.
Check forall n:nat, n = 2.


(* Proofs and evidence *)
Lemma silly : 0 * 3 = 0.
Proof. reflexivity. Qed.

Print silly.


(* Implications are functions *)
Lemma silly_implication: (1 + 1) = 2 -> 0 * 3 = 0.
Proof. intros. reflexivity. Qed.
Print silly_implication.


(* Defining propositions *)


(* Conjugation (logical 'and') *)
Inductive and (P Q : Prop) : Prop :=
  conj : P -> Q -> and P Q.
Notation "P /\ Q" := (and P Q) : type_scope.
Check conj.


(* 'introducing' conjunctions *)
Theorem and_ex: 0 = 0 /\ 4 = mult 2 2.
Proof.
  apply conj.
  reflexivity. reflexivity.
Qed.

Theorem and_ex': 0 = 0 /\ 4 = mult 2 2.
Proof.
  split.
  reflexivity. reflexivity.
Qed.


(* 'eliminating' conjunctions *)
Theorem proj1: forall P Q : Prop,
  P /\ Q -> P.
Proof.
  intros. inversion H as [HP HQ].
  apply HP.
Qed.

(* Exercise: * *)
Theorem proj2 : forall P Q : Prop,
  P /\ Q -> Q.
Proof.
  intros. inversion H.
  apply H1.
Qed.

Theorem and_commut: forall P Q : Prop,
  P /\ Q -> Q /\ P.
Proof.
  intros. inversion H. split.
  apply H1.
  apply H0.
Qed.


(* Exercise: ** *)
Theorem and_assoc: forall P Q R : Prop,
  P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros. inversion H as [HP [HQ HR]]. split. split.
  apply HP.
  apply HQ.
  apply HR.
Qed.


(* Iff *)
Definition iff (P Q : Prop) := (P -> Q) /\ (Q -> P).
Notation "P <-> Q" := (iff P Q) (at level 95, no associativity) : type_scope.

Theorem iff_implies: forall P Q : Prop,
  (P <-> Q) -> P -> Q.
Proof.
  intros P Q H. inversion H as [HPQ HQP].
  apply HPQ.
Qed.

Theorem iff_sym: forall P Q : Prop,
  (P <-> Q) -> (Q <-> P).
Proof.
  intros P Q H. inversion H as [HPQ HQP]. split.
  Case "->". apply HQP.
  Case "<-". apply HPQ.
Qed.


(* Exercise: * *)
Theorem iff_refl: forall P : Prop,
  P <-> P.
Proof.
  intros. split; intros; apply H.
Qed.

Theorem iff_trans: forall P Q R : Prop,
  (P <-> Q) -> (Q <-> R) -> (P <-> R).
Proof.
  intros P Q R HPQP HQRQ.
  inversion HPQP as [HPQ HQP].
  inversion HQRQ as [HQR HRQ].
  split.
  Case "P -> R". intros. apply HQR in HPQ. apply HPQ. apply H.
  Case "P <- R". intros. apply HQP in HRQ. apply HRQ. apply H.
Qed.


(* Disjunction (logical 'or') *)

(* Implementing disjunction *)
Inductive or (P Q : Prop) : Prop :=
| or_introl : P -> or P Q
| or_intror : Q -> or P Q.

Notation "P \/ Q" := (or P Q) : type_scope.

Check or_introl.
Check or_intror.

Theorem or_commut: forall P Q : Prop,
  P \/ Q -> Q \/ P.
Proof.
  intros. inversion H as [HP | HQ].
  Case "left". apply or_intror. apply HP.
  Case "right". apply or_introl. apply HQ.
Qed.

Theorem or_commut': forall P Q : Prop,
  P \/ Q -> Q \/ P.
Proof.
  intros. inversion H as [HP | HQ].
  Case "left". right. apply HP.
  Case "right". left. apply HQ.
Qed.


Theorem or_distributes_over_and_1: forall P Q R : Prop,
  P \/ (Q /\ R) -> (P \/ Q) /\ (P \/ R).
Proof.
  intros. split. inversion H as [HP | [HQ HR]].
  Case "P \/ Q".
    SCase "left". left. apply HP.
    SCase "right". right. apply HQ.
  Case "P \/ R".
    inversion H as [HP | [HQ HR]].
    SCase "left". left. apply HP.
    SCase "right". right. apply HR.
Qed.


(* Exercise: ** *)
Theorem or_distributes_over_and_2: forall P Q R : Prop,
  (P \/ Q) /\ (P \/ R) -> P \/ (Q /\ R).
Proof.
  intros. inversion H as [HPQ HPR].
  inversion HPQ as [HP | HQ].
  Case "left". left. apply HP.
  Case "right". inversion HPR as [HP | HR].
    SCase "left". left. apply HP.
    SCase "right". right. split.
      SSCase "left". apply HQ.
      SSCase "right". apply HR.
Qed.


(* Exercise: * *)
Theorem or_distributes_over_and: forall P Q R : Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  intros. split.
  Case "->". apply or_distributes_over_and_1.
  Case "<-". apply or_distributes_over_and_2.
Qed.


(* Relating /\ and \/ with andb and orb *)
Theorem andb_prop: forall b c,
  andb b c = true -> b = true /\ c = true.
Proof.
  intros. destruct b.
  Case "b=t". destruct c.
    SCase "c=t". split; reflexivity.
    SCase "c=f". inversion H.
  Case "b=f". inversion H.
Qed.

Theorem andb_true_intro: forall b c,
  b = true /\ c = true -> andb b c = true.
Proof.
  intros. inversion H.
  rewrite H0, H1. reflexivity.
Qed.


(* Exercise: ** *)
Theorem andb_false: forall b c,
  andb b c = false -> b = false \/ c = false.
Proof.
  intros. destruct b, c.
  Case "b=t".
    SCase "c=t". inversion H.
    SCase "c=f". right. apply H.
  Case "b=f".
    SCase "c=t". left. apply H.
    SCase "c=f". right. apply H.
Qed.

Theorem orb_prop: forall b c,
  orb b c = true -> b = true \/ c = true.
Proof.
  intros. destruct b.
  Case "b=t". left. reflexivity.
  Case "b=f". right. destruct c.
    SCase "c=t". reflexivity.
    SCase "c=f". inversion H.
Qed.

Theorem orb_false_elim: forall b c,
  orb b c = false -> b = false /\ c = false.
Proof.
  intros. unfold orb in H. destruct b, c.
  Case "b=t".
    SCase "c=t". inversion H.
    SCase "c=f". inversion H.
  Case "b=f".
    SCase "c=t". inversion H.
    SCase "c=f". split; apply H.
Qed.


(* Falsehood *)
Inductive False : Prop :=.

Theorem false_implies_nonsense: False -> 2 + 2 = 5.
Proof.
  intros contra.
  inversion contra.
Qed.

Theorem nonsense_implies_false: 2 + 2 = 5 -> False.
Proof.
  intros contra.
  inversion contra.
Qed.

Theorem ex_falso_quodlibet: forall P : Prop,
  False -> P.
Proof.
  intros P contra.
  inversion contra.
Qed.


(* Truth *)

(* Exercise: ** *)
Inductive True := tt.
(* True isn't used very much on its own (trivial, no useful information)
   Can be useful when defining complex [Prop]s using conditionals or as
   params to higher order [Prop]s. *)


(* Negation *)
Definition not (P:Prop) := P -> False.

Notation "~ x" := (not x) : type_scope.
Check not.

Theorem not_false: ~ False.
Proof.
  unfold not. intros.
  inversion H.
Qed.

Theorem contradiction_implies_anything: forall P Q : Prop,
  (P /\ ~ P) -> Q.
Proof.
  unfold not. intros P Q H. inversion H as [HP HPF].
  apply HPF in HP. inversion HP.
Qed.

Theorem double_neg: forall P : Prop,
  P -> ~ ~ P.
Proof.
  unfold not. intros P H HF.
  apply HF. apply H.
Qed.


(* Exercise: ** *)
Theorem contrapositive: forall P Q : Prop,
  (P -> Q) -> (~Q -> ~P).
Proof.
  unfold not. intros P Q PQ QF H.
  apply QF. apply PQ. apply H.
Qed.

(* Exercise: * *)
Theorem not_both_true_and_false: forall P : Prop,
  ~(P /\ ~P).
Proof.
  unfold not. intros P H. inversion H as [HP HPF].
  apply HPF. apply HP.
Qed.


(* Constructive logic *)
Theorem classic_double_neg: forall P : Prop,
  ~~P -> P.
Proof.
  unfold not. intros.
Abort.

Definition peirce := forall P Q : Prop,
  ((P->Q)->P)->P.

Definition classic := forall P:Prop,
  ~~P -> P.

Definition excluded_middle := forall P,
  P \/ ~P.

Definition de_morgan_not_and_not := forall P Q : Prop,
  ~(~P /\ ~Q) -> P \/ Q.

Definition implies_to_or := forall P Q : Prop,
  (P -> Q) -> (~P \/ Q).


(* Exercise: *** *)
Theorem excluded_middle_irrefutable: forall P:Prop,
  ~~(P \/ ~P).
Proof.
  unfold not. intros. apply H.
  right. intros. apply H.
  left. apply H0.
Qed.


(* Inequality *)
Notation "x <> y" := (~ (x = y)) : type_scope.

(* hint: if the goal state is a contradiction (false = true, say), apply
   ex_falso_quodlibet and change the goal to False. then can use
   assumptions of the form ~P.
*)

Theorem not_false_then_true : forall b:bool,
  b <> false -> b = true.
Proof.
  intros. unfold not in H. destruct b.
  Case "b=t". reflexivity.
  Case "b=f". apply ex_falso_quodlibet. apply H. reflexivity.
Qed.


(* Exercise: ** *)
Theorem false_beq_nat: forall n m : nat,
  n <> m -> beq_nat n m = false.
Proof.
  intros n. induction n.
  Case "n=0".
    simpl. intros. destruct m.
    SCase "m=0". contradiction H. reflexivity.
    SCase "m=S". reflexivity.
  Case "n=S".
    intros. simpl. destruct m.
    SCase "m=0". reflexivity.
    SCase "m=S".
      apply IHn. unfold not in *. intros. apply H. apply f_equal. apply H0.
Qed.

(* Exercise: ** *)
Theorem beq_nat_false: forall n m,
  beq_nat n m = false -> n <> m.
Proof.
  intros n.
  unfold not.
  induction n; destruct m; intros.
  inversion H. inversion H0. inversion H0.
  apply (IHn m). inversion H. reflexivity. inversion H0. reflexivity.
Qed.