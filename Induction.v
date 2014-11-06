(* Chapter 2 Induction *)



Require Export Basics.



(* Naming Cases *)

Require String. Open Scope string_scope.

Ltac move_to_top x :=
  match reverse goal with
  | H : _ |- _ => try move x after H
  end.

Tactic Notation "assert_eq" ident(x) constr(v) :=
  let H := fresh in
  assert (x = v) as H by reflexivity;
  clear H.

Tactic Notation "Case_aux" ident(x) constr(name) :=
  first [
    set (x := name); move_to_top x
  | assert_eq x name; move_to_top x
  | fail 1 "because we are working on a different case" ].

Tactic Notation "Case" constr(name) := Case_aux Case name.
Tactic Notation "SCase" constr(name) := Case_aux SCase name.
Tactic Notation "SSCase" constr(name) := Case_aux SSCase name.
Tactic Notation "SSSCase" constr(name) := Case_aux SSSCase name.
Tactic Notation "SSSSCase" constr(name) := Case_aux SSSSCase name.
Tactic Notation "SSSSSCase" constr(name) := Case_aux SSSSSCase name.
Tactic Notation "SSSSSSCase" constr(name) := Case_aux SSSSSSCase name.
Tactic Notation "SSSSSSSCase" constr(name) := Case_aux SSSSSSSCase name.


Theorem andb_true_elim1 : forall b c : bool,
                            andb b c = true -> b = true.
Proof.
  intros b c H.
  destruct b.
  Case "b = true".
    reflexivity.
  Case "b = false".
    rewrite <- H. reflexivity.
Qed.


(* Exercise: ** andb_true_elim2 *)
Theorem andb_true_elim2 : forall b c : bool,
                            andb b c = true -> c = true.
Proof.
  intros b c H.
  destruct c.
  Case "c = true".
    reflexivity.
  Case "c = false".
    destruct b.
    SCase "b = true".
      rewrite <- H. reflexivity.
    SCase "b = false".
      rewrite <- H. reflexivity.
Qed.



(* Proof by Induction *)

Theorem plus_0_r_firsttry : forall n : nat,
                              n + 0 = n.
Proof.
  intros n.
  simpl.
Abort.

Theorem plus_0_r_secondtry : forall n : nat,
                               n + 0 = n.
Proof.
  intros n. destruct n as [| n'].
  Case "n = 0".
    reflexivity.
  Case "n = S n'".
    simpl.
Abort.


Theorem plus_0_r : forall n : nat, n + 0 = n.
Proof.
  intros n. induction n as [| n'].
  Case "n = 0".
    reflexivity.
  Case "n = S n'".
    simpl. rewrite IHn'. reflexivity.
Qed.

Theorem minus_diag : forall n, minus n n = 0.
Proof.
  intros n. induction n as [| n'].
  Case "n = 0".
    reflexivity.
  Case "n = S n'".
    simpl. rewrite IHn'. reflexivity.
Qed.


(* Exercise: ** basic induction *)

Theorem mult_0_r : forall n : nat, n * 0 = 0.
Proof.
  intros n. induction n as [| n'].
  Case "n = 0".
    reflexivity.
  Case "n = S n'".
    simpl. rewrite IHn'. reflexivity.
Qed.

Theorem plus_n_Sm : forall n m : nat, S (n + m) = n + S m.
Proof.
  intros n m. induction n as [| n'].
  Case "n = 0".
    reflexivity.
  Case "n = S n'".
    simpl. rewrite IHn'. reflexivity.
Qed.

Theorem plus_comm : forall n m : nat, n + m = m + n.
Proof.
  intros n m. induction n as [| n'].
  Case "n = 0".
    rewrite plus_0_r. reflexivity.
  Case "n = S n'".
    rewrite <- plus_n_Sm. rewrite <- IHn'. reflexivity.
Qed.

Theorem plus_assoc : forall n m p : nat, n + (m + p) = (n + m) + p.
Proof.
  intros n m p. induction n as [| n'].
  Case "n = 0".
    reflexivity.
  Case "n = S n'".
    simpl. rewrite IHn'. reflexivity.
Qed.


(* Exercise: ** double plus *)
Fixpoint double (n:nat) :=
  match n with
    | O => O
    | S n' => S (S (double n'))
  end.

Theorem double_plus : forall n, double n = n + n.
Proof.
  intros n. induction n as [| n'].
  Case "n = 0".
    reflexivity.
  Case "n = S".
    simpl. rewrite IHn'. rewrite plus_n_Sm. reflexivity.
Qed.


(* Exercise: * destruct induction

   [destruct] and [induction] both split a value into its separate constructors.
   Creating subgoals for each constructor.

   They differ in that [induction] adds an induction hypothesis to the context
   [destruct] does not add an induction hypothesis.
 *)



(* Proofs within Proofs *)

Theorem mult_0_plus' : forall n m : nat, (0 + n) * m = n * m.
Proof.
  intros n m.
  assert (H: 0 + n = n).
    Case "Proof of assertion". reflexivity.
  rewrite H. reflexivity.
Qed.

Theorem plus_rearrange_firsttry : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  (* need to swap (n + m) with (m + n) *)
  rewrite plus_comm.
  (* swapped the *outer* plus: (p+q) + (n+m)... *)
Abort.

Theorem plus_rearrange : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  assert (H: n + m = m + n).
  Case "Proof of assertion".
    rewrite plus_comm. reflexivity.
  rewrite H. reflexivity.
Qed.



(* Exercise: **** mult comm *)
Theorem plus_swap : forall n m p : nat, n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  assert (H: n + m = m + n).
  Case "Proof of assertion".
    rewrite plus_comm. reflexivity.
  rewrite plus_assoc. rewrite H. rewrite plus_assoc. reflexivity.
Qed.


Theorem mult_plus : forall n m : nat, n * S m = n + (n * m).
Proof.
  intros n m.
  induction n as [| n'].
  Case "n = 0".
    reflexivity.
  Case "n = S".
    simpl. rewrite IHn'. rewrite plus_swap. reflexivity.
Qed.

Theorem mult_comm : forall m n : nat, m * n = n * m.
Proof.
  intros m n. induction m as [| m'].
  Case "m = 0".
    rewrite mult_0_r. reflexivity.
  Case "m = S".
    simpl. rewrite mult_plus. rewrite IHm'. reflexivity.
Qed.


(* Exercise: ** optional evenb n oddb S n *)
Theorem evenb_n_oddb_Sn : forall n : nat, evenb n = negb (evenb (S n)).
Proof.
  intros n. induction n as [| n'].
  Case "n = 0".
    reflexivity.
  Case "n = S".
    simpl. rewrite IHn'. rewrite negb_involutive. reflexivity.
Qed.



(* More Exercises *)

(* Exercise: *** optional more exercises *)

(* Guess: simplification *)
Theorem ble_nat_refl : forall n : nat,
  true = ble_nat n n.
Proof.
  intros. induction n as [| n'].
  Case "n = 0".
    reflexivity.
  Case "n = S".
    rewrite IHn'. reflexivity.
Qed.
(* Guessed wrong. [ble_nat] is defined as recursive... use induction on that? *)

(* Guess: Even though recursively defined, I'll guess destruct is required *)
Theorem zero_nbeq_S : forall n : nat,
  beq_nat 0 (S n) = false.
Proof.
  reflexivity.
Qed.
(* Guessed wrong. only needed simpl/reflexivity... *)

(* Guess: simpl/reflexivity *)
Theorem andb_false_r : forall b : bool,
  andb b false = false.
Proof.
  destruct b. reflexivity. reflexivity.
Qed.
(* Guessed wrong: needed destruct *)

(* Guess: induction required *)
Theorem plus_ble_compat_l : forall n m p : nat,
  ble_nat n m = true -> ble_nat (p + n) (p + m) = true.
Proof.
  intros. induction p as [| n'].
  Case "p = 0".
    simpl. rewrite H. reflexivity.
  Case "P = S".
    simpl. rewrite IHn'. reflexivity.
Qed.
(* Guessed correctly *)


(* Guess: simpl/reflexivity. Same as other beq_nat proof. *)
Theorem S_nbeq_0 : forall n : nat,
  beq_nat (S n) 0 = false.
Proof.
  reflexivity.
Qed.
(* Guessed correct *)


(* Guess: induction required *)
Theorem mult_1_l : forall n : nat, 1 * n = n.
Proof.
  intros. destruct n. reflexivity.
  simpl. rewrite plus_0_r. reflexivity.
Qed.
(* Guessed wrong... dammit *)

(* Guess: destruct required. Bools aren't inductively defined *)
Theorem all3_spec : forall b c : bool,
  orb (andb b c)
      (orb (negb b)
           (negb c)) = true.
Proof.
  intros. destruct b.
  Case "b = true".
    destruct c. reflexivity. reflexivity.
  Case "b = false".
    reflexivity.
Qed.
(* Guessed correctly *)

(* Guess: induction required *)
Theorem mult_plus_distr_r : forall n m p : nat,
  (n + m) * p = (n * p) + (m * p).
Proof.
  intros.
  induction n.
  Case "n=0".
    reflexivity.
  Case "n=S".
    simpl. rewrite IHn. rewrite plus_assoc. reflexivity.
Qed.
(* could this be done without induction? *)

(* Guess: induction *)
Theorem mult_assoc : forall n m p : nat,
  n * (m * p) = (n * m) * p.
Proof.
  intros n m p. induction n.
  Case "n=0".
    reflexivity.
  Case "n=S".
    simpl. rewrite IHn. rewrite mult_plus_distr_r. reflexivity.
Qed.
(* induction it seems *)



(* Exercise: ** optional beq_nat_refl *)
Theorem beq_nat_refl : forall n : nat,
  true = beq_nat n n.
Proof.
  intros. induction n.
  Case "n=0".
    reflexivity.
  Case "n=S".
    simpl. rewrite IHn. reflexivity.
Qed.


(* Exercise: ** optional plus_swap' *)
Theorem plus_swap' : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  intros.
  rewrite plus_assoc. rewrite plus_assoc.
  replace (n+m) with (m+n). reflexivity.
    Case "Proof of replace". rewrite plus_comm. reflexivity.
Qed.


(* Exerice: *** binary_commute *)
Theorem bin_unary_comm : forall n : bin,
  bin_to_nat (increment n) = plus 1 (bin_to_nat n).
Proof.
  intros. induction n.
  Case "n=zero".
    reflexivity.
  Case "n=Twice".
    reflexivity.
    Case "n=twicePlus1".
    simpl. rewrite IHn. simpl. rewrite <- plus_n_Sm. reflexivity.
Qed.