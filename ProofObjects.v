(* Chapter 10 Proof Objects Working with explicit evidence in coq *)

Require Export MoreLogic.

Print beautiful.
Check bsum.

Theorem eight_is_beautiful: beautiful 8.
Proof.
  apply bsum with (n:=3).
  apply b3.
  apply b5.
Qed.
Print eight_is_beautiful.

Check bsum 3 5 b3 b5.

Theorem eight_is_beautiful': beautiful 8.
Proof.
  apply (bsum 3 5 b3 b5).
Qed.


(* Proof scripts and proof objects *)
Theorem eight_is_beautiful'': beautiful 8.
Proof.
  Show Proof.
  apply bsum with (n:=3).
  Show Proof.
  apply b3.
  Show Proof.
  apply b5.
  Show Proof.
Qed.

Definition eight_is_beautiful''' : beautiful 8 := bsum 3 5 b3 b5.

Print eight_is_beautiful.
Print eight_is_beautiful'.
Print eight_is_beautiful''.
Print eight_is_beautiful'''.

(* Exercise: * *)
Theorem six_is_beautiful: beautiful 6.
Proof.
  apply bsum with (n:=3).
  apply b3. apply b3.
Qed.

Definition six_is_beautiful' : beautiful 6 := bsum 3 3 b3 b3.

(* Exercise: * *)
Theorem nine_is_beautiful : beautiful 9.
Proof.
  apply bsum with (n:=3). apply b3.
  apply bsum with (n:=3); apply b3.
Qed.

Definition nine_is_beautiful': beautiful 9 := bsum 3 6 b3 (bsum 3 3 b3 b3).


(* Quantification, implications and functions *)
Theorem b_plus3: forall n, beautiful n -> beautiful (3 + n).
Proof.
  intros. apply bsum. apply b3. apply H.
Qed.
Print b_plus3.

Definition b_plus3': forall n, beautiful n -> beautiful (3 + n) :=
  fun (n:nat) => fun (H:beautiful n) => bsum 3 n b3 H.
Check b_plus3'.

Definition b_plus3'' (n:nat) (H:beautiful n) : beautiful (3 + n) :=
  bsum 3 n b3 H.
Check b_plus3''.

Definition beautiful_plus3 : Prop :=
  forall n, forall (E:beautiful n), beautiful (n+3).

Definition beautiful_plus3' : Prop :=
  forall n, forall (_:beautiful n), beautiful (n+3).

Definition beautiful_plus3'' : Prop :=
  forall n, beautiful n -> beautiful (n+3).

(* in general, [P -> Q] is just syntactic sugar for [forall (_:P), Q] *)

(* Exercise: ** *)
Definition b_times2' : forall n, beautiful n -> beautiful (2 * n) :=
  fun (n:nat) => fun (H:beautiful n) => bsum n (n + 0) H (bsum n 0 H b0).


(* Exercise: ** *)
SearchAbout gorgeous.
Definition gorgeous_plus13_po: forall n, gorgeous n -> gorgeous (13+n) :=
  fun (n:nat) => fun (g:gorgeous n) => g5 (8 + n) (g5 (3 + n) (g3 n g)).


Theorem and_example: beautiful 0 /\ beautiful 3.
Proof.
  apply conj. apply b0. apply b3.
Qed.
Print and_example.
(*
   conj (beautiful 0) (beautiful 3) b0 b3 : beautiful 0 /\ beautiful 3
*)

(* Exercise: * optional *)
Theorem and_example': beautiful 0 /\ beautiful 3.
Proof.
  apply conj.
  Case "left". apply b0.
  Case "right". apply b3.
Qed.
Print and_example'.
(*
   conj (beautiful 0)
        (beautiful 3)
        (let Case := "left" in b0)
        (let Case := "right" in b3)
   : beautiful 0 /\ beautiful 3
*)


Theorem and_commut: forall P Q : Prop,
  P /\ Q -> Q /\ P.
Proof.
  intros. Show Proof.
  inversion H as [HP HQ]. Show Proof.
  split. Show Proof.
  apply HQ. Show Proof.
  apply HP. Show Proof.
Qed.
Print and_commut.


(* Exercise: ** *)
Definition conj_fact': forall P Q R,  P /\ Q -> Q /\ R -> P /\ R.
Proof.
  intros p q r hpq hqr.
  inversion hpq.
  split. apply H.
  inversion hqr.
  apply H2.
Qed.
Print conj_fact'.

Definition conj_fact : forall P Q R, P /\ Q -> Q /\ R -> P /\ R :=
  fun (P Q R : Prop) (hpq:P/\Q) (hqr:Q/\R) =>
    match hpq, hqr with
      | conj p q, conj q2 r => conj P R p r
    end.

(* Exercise: ** *)
Definition beautiful_iff_gorgeous: forall n, beautiful n <-> gorgeous n.
Proof.
  split.
  Case "->". intros. induction H.
    SCase "g0". apply g0.
    SCase "g3". apply g3. apply g0.
    SCase "g5". apply g5. apply g0.
    SCase "gsum". apply gorgeous_sum. apply IHbeautiful1. apply IHbeautiful2.
  Case "<-". intros. induction H.
    SCase "b0". apply b0.
    SCase "b3". apply bsum with (n:=3). apply b3. apply IHgorgeous.
    SCase "b5". apply bsum with (n:=5). apply b5. apply IHgorgeous.
Qed.
Print beautiful_iff_gorgeous.

(* Exercise: ** *)
Definition or_commut: forall P Q : Prop, P \/ Q -> Q \/ P :=
  fun (P Q : Prop) (pq: P\/Q) =>
    match pq with
      | or_introl p => or_intror Q P p
      | or_intror q => or_introl Q P q
    end.
Print or_commut.


Check ex.
Definition some_nat_is_even : Prop := ex _ ev.

Definition snie : some_nat_is_even := ex_intro _ ev 4 (ev_SS 2 (ev_SS 0 ev_0)).

(* Exercise: ** optional *)
Definition p : ex _ (fun n => beautiful (S n)) := ex_intro _ _ 2 b3.
Print p.

(* Giving explicit arguments to lemmas and hypotheses *)
Check plus_comm.

Lemma plus_comm_r : forall a b c, c + (b + a) = c + (a + b).
Proof.
  intros.
  rewrite (plus_comm b). (* only one subexpression with b can be rewritten *)
  (* rewrite (plus_comm b a) *) (* so don't need the extra a *)
  reflexivity.
Qed.

Lemma plus_comm_r' : forall a b c, c + (b + a) = c + (a + b).
Proof.
  intros.
  rewrite (plus_comm _ a). (* _ coq can infer easy arguments *)
  reflexivity.
Qed.

Lemma plus_comm_r'' : forall a b c, c + (b + a) = c + (a + b).
Proof.
  intros.
  rewrite plus_comm with (n:=b). (* named arguments rather than the above which
                                    is by position *)
  reflexivity.
Qed.


Example trans_eq_ex: forall a b c d e f : nat,
  [a;b] = [c;d] ->
  [c;d] = [e;f] ->
  [a;b] = [e;f].
Proof.
  intros.
  apply (trans_eq (list nat) _ [c;d]). (* somehow can't infer the type *)
  apply H. apply H0.
Qed.


(* Programming with tactics *)
Definition add1: nat -> nat. (* ending with . rather than := tells coq to enter
                                proof script mode *)
intros n. Show Proof.
apply S. Show Proof.
apply n. Show Proof.
Defined.

Print add1.
            (* add1 = fun n : nat => S n : nat -> nat *)
Eval compute in add1 2.