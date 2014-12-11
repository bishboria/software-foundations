(* Chapter 8 Propositions and evidence *)

Require Export Logic Induction.

(* from boolean functions to propositions *)
Definition even (n:nat) : Prop :=
  evenb n = true.

(* inductively defined propositions *)
Inductive ev: nat -> Prop :=
  | ev_0  : ev 0
  | ev_SS : forall n:nat, ev n -> ev (S (S n)).

(* Exercise: * *)
Theorem double_even: forall n,
  ev (double n).
Proof.
  intros. induction n.
  Case "n=0". apply ev_0.
  Case "n=S". apply ev_SS. apply IHn.
Qed.


(* computational vs inductive definitions *)

(* sometimes it's preferable to write a testing function to check a boolean
   property. this may not always be possible however. other times it's
   preferable to encode the property directly as an inductive definition
*)

(* Exercise: * *)
Theorem ev__even: forall n,
  ev n -> even n.
Proof.
  intros n e. induction e.
  Case "e=0". reflexivity.
  Case "e=S". unfold even in *. apply IHe.
Qed.

(* to be explained later: induction principle on inductively defined
   propositions does not follow quite the same form as that of inductively
   defined sets
*)

(* Exercise: * *)
Theorem will_not_succeed: forall n, ev n.
Proof.
  intros. induction n.
  Case "O". apply ev_0.
  Case "S".
Abort.
(* There's no way to have ev n and ev (S n) *)

(* Exercise: ** *)
Theorem ev_sum: forall n m,
  ev n -> ev m -> ev (n + m).
Proof.
  intros n m en em. induction en.
  Case "O". apply em.
  Case "S". apply ev_SS. apply IHen.
Qed.


(* Example: beautiful numbers *)

Inductive beautiful : nat -> Prop :=
| b0   : beautiful 0
| b3   : beautiful 3
| b5   : beautiful 5
| bsum : forall n m, beautiful n -> beautiful m -> beautiful (n + m).

Theorem three_is_beautiful: beautiful 3.
Proof. apply b3. Qed.

Theorem eight_is_beautiful: beautiful 8.
Proof.
  apply bsum with (n:=3).
  apply b3. apply b5.
Qed.

Theorem beautiful_plus_eight: forall n,
  beautiful n -> beautiful (8 + n).
Proof.
  intros. apply bsum with (n:=8).
  apply eight_is_beautiful.
  apply H.
Qed.


(* Exercise: ** *)
Theorem b_times2: forall n, beautiful n -> beautiful (2 * n).
Proof.
  intros. induction H.
  Case "0". apply b0.
  Case "3". simpl. apply bsum with (n:=3). apply b3. apply b3.
  Case "5". simpl. apply bsum with (n:=5). apply b5. apply b5.
  Case "+". apply bsum with (n:=n+m).
    apply bsum. apply H. apply H0.
    apply bsum with (n:=n+m). apply bsum. apply H. apply H0. apply b0.
Qed.

(* Exercise: *** *)
Theorem b_times_m: forall n m,
  beautiful n -> beautiful (m * n).
Proof.
  intros n m bn. induction m.
  Case "m=0". apply b0.
  Case "m=S". apply bsum with (n:=n). apply bn. apply IHm.
Qed.


(* Induction over evidence *)
Inductive gorgeous : nat -> Prop :=
| g0 : gorgeous 0
| g3 : forall n, gorgeous n -> gorgeous (3 + n)
| g5 : forall n, gorgeous n -> gorgeous (5 + n).

(* Exercise: * *)
Theorem gorgeous_plus13: forall n,
  gorgeous n -> gorgeous (13 + n).
Proof.
  intros. apply g3. apply g5. apply g5. apply H.
Qed.


Theorem gorgeous__beautiful: forall n,
  gorgeous n -> beautiful n.
Proof.
  intros. induction H.
  Case "g0". apply b0.
  Case "g3". apply bsum. apply b3. apply IHgorgeous.
  Case "g5". apply bsum. apply b5. apply IHgorgeous.
Qed.


Theorem gorgeous__beautiful_failed: forall n,
  gorgeous n -> beautiful n.
Proof.
  intros. induction n. apply b0.
  (* Stuck on: beautiful (S n) *)
Abort.


(* Exercise: ** *)
Theorem gorgeous_sum: forall n m,
  gorgeous n -> gorgeous m -> gorgeous (n + m).
Proof.
  intros n m gn gm. induction gn.
  Case "g0". apply gm.
  Case "g3". apply g3, IHgn.
  Case "g5". apply g5, IHgn.
Qed.

(* Exercise: *** advanced *)
Theorem beautiful__gorgeous: forall n,
  beautiful n -> gorgeous n.
Proof.
  intros n bn. induction bn.
  Case "b0". apply g0.
  Case "b3". apply g3, g0.
  Case "b5". apply g5, g0.
  Case "b+". apply gorgeous_sum. apply IHbn1. apply IHbn2.
Qed.


(* Exercise: *** *)
Theorem g_times2: forall n, gorgeous n -> gorgeous (2 * n).
Proof.
  intros n gn. destruct gn.
  Case "g0". apply g0.
  Case "g3".
    apply gorgeous_sum. apply g3. apply gn.
    apply gorgeous_sum. apply g3. apply gn. apply g0.
  Case "g5".
    apply gorgeous_sum. apply g5. apply gn.
    apply gorgeous_sum. apply g5. apply gn. apply g0.
Qed.



(* Inversion on evidence *)
Theorem ev_minus2: forall n,
  ev n -> ev (pred (pred n)).
Proof.
  intros n evn. inversion evn.
  Case "0". apply ev_0.
  Case "S". apply H.
Qed.

(* Exercise: * *)
Theorem ev_minus2_destruct: forall n,
  ev n -> ev (pred (pred n)).
Proof.
  intros n evn. destruct evn.
  Case "0". apply ev_0.
  Case "S". apply evn.
Qed.

Theorem SSev__even: forall n,
  ev (S (S n)) -> ev n.
Proof.
  intros n essn. inversion essn as [|n' e']. apply e'.
Qed.


(* inversion revisited *)

(* Exercise: * *)
Theorem SSSSev__even: forall n,
  ev (S (S (S (S n)))) -> ev n.
Proof.
  intros. inversion H. inversion H1. apply H3.
Qed.

Theorem even5_nonsense: ev 5 -> 2 + 2 = 9.
Proof.
  intros. inversion H. inversion H1. inversion H3.
Qed.


(* Exercise: *** advanced *)
Theorem ev_ev__ev: forall n m,
  ev (n+m) -> ev n -> ev m.
Proof.
  intros n m evnm en. induction en as [|n' evn' ihen'].
  Case "0". apply evnm.
  Case "S".
    apply ihen'. simpl in evnm. apply SSev__even, evnm.
Qed.


(* Exercise: *** optional *)
Theorem ev_plus_plus: forall n m p,
  ev (n+m) -> ev (n+p) -> ev (m+p).
Proof.
  intros n m p evnm evnp.
  apply ev_ev__ev with n. rewrite plus_assoc.
  apply ev_sum. apply evnm.

  apply ev_ev__ev with n. apply evnp.
  apply ev_ev__ev with m. rewrite plus_comm. apply evnm.
Abort.



(* Additional exercises *)

(* Exercise: ** *)
Inductive R : nat -> list nat -> Prop :=
| c1 : R 0 []
| c2 : forall n l, R n l -> R (S n) (n :: l)
| c3 : forall n l, R (S n) l -> R n l.

(* Which of * are provable:
   R 2 [1,0]
   R 1 [1,2,1,0]
   R 6 [3,2,1,0]
*)
Definition t1 := c1.                Check t1.
Definition t2 := c2 0 [] t1.        Check t2.
Definition t3 := c2 1 [0] t2.       Check t3. (* R 2 [1;0] *)
Definition t4 := c2 2 [1;0] t3.     Check t4.
Definition t5 := c3 2 [2;1;0] t4.   Check t5.
Definition t6 := c3 1 [2;1;0] t5.   Check t6.
Definition t7 := c2 1 [2;1;0] t6.   Check t7.
Definition t8 := c3 1 [1;2;1;0] t7. Check t8. (* R 1 [1;2;1;0] *)
(* Can't construct the last one. the number should be up-to 1 more than the head
   of the list
*)



(* Relations *)
Inductive le : nat -> nat -> Prop :=
| le_n : forall n, le n n
| le_s : forall n m, le n m -> le n (S m).
Notation "m <= n" := (le m n).

(* rest of chapter is basically the Rel chapter... *)