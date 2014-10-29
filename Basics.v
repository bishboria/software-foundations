(* Chapter 1 Basics *)

Inductive day : Type :=
| monday : day
| tuesday : day
| wednesday : day
| thursday : day
| friday : day
| saturday : day
| sunday : day.

Check day_rect.  (* types *)
Check day_ind.   (* props *)
Check day_rec.   (* sets  *)

Definition next_weekday (d:day) : day :=
  match d with
    | monday    => tuesday
    | tuesday   => wednesday
    | wednesday => thursday
    | thursday  => friday
    | _         => monday
  end.

Eval compute in next_weekday friday. (* monday *)
Eval compute in next_weekday (next_weekday saturday). (* tuesday *)

Example test_next_weekday : next_weekday (next_weekday saturday) = tuesday.
Proof. simpl. reflexivity. Qed.

Extraction next_weekday. (* Extracts the ocaml version of next_weekday *)


(* Booleans *)

Inductive bool : Type :=
| true : bool
| false : bool.

Definition negb (b:bool) : bool :=
  match b with
    | true => false
    | false => true
  end.

Definition andb (b1 b2 : bool) : bool :=
  match b1 with
    | true => b2
    | false => false
  end.

Definition orb (b1 b2 : bool) : bool :=
  match b1 with
    | true => true
    | false => b2
  end.

Example test_orb1: orb true false = true.
Proof. reflexivity. Qed.

Example test_orb2: orb false false = false.
Proof. reflexivity. Qed.

Example test_orb3: orb false true = true.
Proof. reflexivity. Qed.

Example test_orb4: orb true true = true.
Proof. reflexivity. Qed.


(* Exercise: * nandb *)
Definition nandb (b1 b2 : bool) : bool :=
  match b1, b2 with
    | true, true => false
    | _,    _    => true
  end.

Example test_nandb1: nandb true false = true.
Proof. reflexivity. Qed.

Example test_nandb2: nandb false false = true.
Proof. reflexivity. Qed.

Example test_nandb3: nandb false true = true.
Proof. reflexivity. Qed.

Example test_nandb4: nandb true true = false.
Proof. reflexivity. Qed.

(* Exercise: * andb3 *)
Definition andb3 (b1 b2 b3 : bool) : bool :=
  match b1, b2, b3 with
    | true, true, true => true
    | _,    _,    _    => false
  end.

Example test_andb31: andb3 true true true = true.
Proof. reflexivity. Qed.

Example test_andb32: andb3 false true true = false.
Proof. reflexivity. Qed.

Example test_andb33: andb3 true false true = false.
Proof. reflexivity. Qed.

Example test_andb34: andb3 true true false = false.
Proof. reflexivity. Qed.


(* Function Types *)

Check true.        (* bool *)
Check (negb true). (* bool *)
Check negb.        (* bool -> bool *)
Check andb.        (* bool -> bool -> bool *)


(* Numbers *)

Module Playground1.

  Inductive nat : Type :=
    | O : nat
    | S : nat -> nat.

  Definition pred (n:nat) : nat :=
    match n with
      | O    => O
      | S n' => n'
    end.
End Playground1.

Definition minustwo (n:nat) : nat :=
  match n with
    | O        => O
    | S O      => O
    | S (S n') => n'
  end.

Check S (S (S (S O))).      (* 4 : nat *)
Eval compute in minustwo 4. (* 2 : nat *)

Check S.        (* nat -> nat *)
Check pred.     (* nat -> nat *)
Check minustwo. (* nat -> nat *)

Fixpoint evenb (n:nat) : bool :=
  match n with
    | O        => true
    | S O      => false
    | S (S n') => evenb n'
  end.

Definition oddb (n:nat) : bool := negb (evenb n).

Example test_oddb1: oddb (S O) = true.
Proof. reflexivity. Qed.

Example test_oddb2: oddb (S (S (S (S 0)))) = false.
Proof. reflexivity. Qed.


Module Playground2.
  Fixpoint plus (n m : nat) : nat :=
    match n with
      | O    => m
      | S n' => S (plus n' m)
    end.

  Eval compute in plus (S (S (S O))) (S (S O)).

  Fixpoint mult (n m : nat) : nat :=
    match n with
      | O    => O
      | S n' => plus m (mult n' m)
    end.

  Example test_mult1: mult 3 3 = 9.
  Proof. reflexivity. Qed.

  Fixpoint minus (n m : nat) : nat :=
    match n, m with
      | O, _ => O
      | _, O => n
      | S n', S m' => minus n' m'
    end.
End Playground2.

Fixpoint exp (base power : nat) : nat :=
  match power with
    | O   => S O
    | S p => mult base (exp base p)
  end.

(* Exercise: * factorial *)
Fixpoint factorial (n:nat) : nat :=
  match n with
    | O    => S O
    | S n' => mult n (factorial n')
  end.

Example test_factorial1: factorial 3 = 6.
Proof. reflexivity. Qed.

Example test_factorial2: factorial 5 = mult 10 12.
Proof. reflexivity. Qed.

Notation "x + y" := (plus x y) (at level 50, left associativity) : nat_scope.
Notation "x - y" := (minus x y) (at level 50, left associativity) : nat_scope.
Notation "x * y" := (mult x y) (at level 40, left associativity) : nat_scope.

Check ((0 + 1) + 1).

Fixpoint beq_nat (n m : nat) : bool :=
  match n, m with
    | O, O       => true
    | S n', S m' => beq_nat n' m'
    | _, _       => false
  end.

Fixpoint ble_nat (n m : nat) : bool :=
  match n, m with
    | O, _       => true
    | S n', S m' => ble_nat n' m'
    | _, _       => false
  end.

Example test_ble_nat1: ble_nat 2 2 = true.
Proof. reflexivity. Qed.

Example test_ble_nat2: ble_nat 2 4 = true.
Proof. reflexivity. Qed.

Example test_ble_nat3: ble_nat 4 2 = false.
Proof. reflexivity. Qed.


(* Exerice: ** blt_nat *)
Definition blt_nat (n m : nat) : bool :=
  andb (ble_nat n m) (negb (beq_nat n m)).

Example test_blt_nat1: blt_nat 2 2 = false.
Proof. reflexivity. Qed.

Example test_blt_nat2: blt_nat 2 4 = true.
Proof. reflexivity. Qed.

Example test_blt_nat3: blt_nat 4 2 = false.
Proof. reflexivity. Qed.


(* Proof by Simplification *)

Theorem plus_0_n : forall n:nat, 0 + n = n.
Proof.
  intros n. reflexivity. Qed.

(* Theorem, Example, Lemma, Fact, Remark: all meant the same thing to Coq. *)

Theorem plus_1_l : forall n:nat, 1 + n = S n.
Proof.
  intros n. reflexivity. Qed.

Theorem mult_0_l : forall n:nat, 0 * n = 0.
Proof.
  intros n. reflexivity. Qed.


(* Proof by Rewriting *)

Theorem plus_id_example : forall n m : nat,
                            n = m ->
                            n + n = m + m.
Proof.
  intros n m.   (* Introduce things into the context *)
  intros H.     (* Introduce hypothesis into the context, and call it H *)
  rewrite -> H. (* Replace LHS H with RHS H in the goal *)
  reflexivity.
Qed.


(* Exercise: * plus_id_exercise *)
Theorem plus_id_exercise : forall n m o : nat,
                             n = m -> m = o -> n + m = m + o.
Proof.
  intros n m o.
  intros H1 H2.
  rewrite H1. rewrite <- H2.
  reflexivity.
Qed.


Theorem mult_0_plus : forall n m : nat,
                        (0 + n) * m = n * m.
Proof.
  intros n m.
  rewrite plus_0_n.
  reflexivity.
Qed.


(* Exercise: ** mult_S_1 *)
Theorem mult_S_1 : forall n m : nat,
                     m = S n ->
                     m * (1 + n) = m * m.
Proof.
  intros n m.
  intros H.
  rewrite plus_1_l.
  rewrite <- H.
  reflexivity.
Qed.


(* Proof by Case Analysis *)

Theorem plus_1_neq_0_firsttry : forall n:nat,
                                  beq_nat (n + 1) 0 = false.
Proof.
  intros n.
  simpl. (* does nothing *)
Abort.

Theorem plus_1_neq_0 : forall n:nat,
                         beq_nat (n + 1) 0 = false.
Proof.
  intros n.
  destruct n as [| n'].
  reflexivity.
  reflexivity.
Qed.


Theorem negb_involutive : forall b:bool,
                            negb (negb b) = b.
Proof.
  intros b.
  destruct b.
  reflexivity. reflexivity.
Qed.


(* Exercise: * zero_nbeq_plus_1 *)
Theorem zero_nbeq_plus_1 : forall n:nat,
                             beq_nat 0 (n + 1) = false.
Proof.
  intros n.
  destruct n as [| n'].
  reflexivity.
  reflexivity.
Qed.


(* More Exercises *)

(* Exercise: ** boolean functions *)
Theorem identity_fn_applied_twice : forall (f : bool -> bool),
                                    (forall (x : bool), f x = x) ->
                                    forall b:bool, f (f b) = b.
Proof.
  intros.
  destruct b.
  rewrite H. rewrite H. reflexivity.
  rewrite H. rewrite H. reflexivity.
Qed.

Theorem negation_fn_applied_twice :  forall (f : bool -> bool),
                                    (forall (x : bool), f x = negb x) ->
                                    forall b:bool, f (f b) = b.
Proof.
  intros.
  destruct b.
  rewrite H. rewrite H. rewrite negb_involutive. reflexivity.
  rewrite H. rewrite H. rewrite negb_involutive. reflexivity.
Qed.


(* Exercise: ** andb_eq_orb *)
Theorem andb_eq_orb : forall b c : bool,
                        andb b c = orb b c ->
                        b = c.
Proof.
  intros b c.
  destruct b.
  destruct c.
  intros H. reflexivity.
  intros H. simpl in H. rewrite H. reflexivity.

  destruct c.
  intros H. simpl in H. rewrite H. reflexivity.
  intros H. reflexivity.
Qed.


(* Exercise: *** binary *)
Inductive bin : Type :=
| zero       : bin
| twice      : bin -> bin
| twicePlus1 : bin -> bin.

Fixpoint increment (b:bin) : bin :=
  match b with
    | zero          => twicePlus1 b
    | twice b'      => twicePlus1 b'
    | twicePlus1 b' => twice (increment b')
  end.

Fixpoint bin_to_nat (b:bin) : nat :=
  match b with
    | zero          => O
    | twice b'      => mult 2 (bin_to_nat b')
    | twicePlus1 b' => plus 1 (mult 2 (bin_to_nat b'))
  end.

Example inc_bin_to_nat_1 : bin_to_nat (increment zero) = 1.
Proof. reflexivity. Qed.

Example inc_bin_to_nat_2 : bin_to_nat (increment (twice zero)) = 1.
Proof. reflexivity. Qed.

Example inc_bin_to_nat_3 : bin_to_nat (increment (twicePlus1 zero)) = 2.
Proof. reflexivity. Qed.

Example inc_bin_to_nat_4 : bin_to_nat (increment (twice (twicePlus1 zero))) = 3.
Proof. reflexivity. Qed.

Example inc_bin_to_nat_5 :
  bin_to_nat (increment (twice (twice (twicePlus1 zero)))) = 5.
Proof. reflexivity. Qed.


(* Exercise: ** optional decreasing *)

(* Write a simple fixpoint function on numbers that does terminate on all inputs
   but Coq won't accept because a term isn't decreasing
*)
Fixpoint not_zero (n:nat) : nat :=
  match n with
    | O    => not_zero (S n) (* increases *)
    | S n' => S n'           (* returns same thing *)
  end.