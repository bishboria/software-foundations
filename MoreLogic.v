(* Chapter 9 More Logic *)

Require Export "Prop".

(* Existential quantification *)
Inductive ex (X:Type) (P:X -> Prop) : Prop :=
  ex_intro : forall witness:X, P witness -> ex X P.

Notation "'exists' x , p" :=
  (ex _ (fun x => p))
  (at level 200, x ident, right associativity) : type_scope.
Notation "'exists' x : X , p" :=
  (ex _ (fun x:X => p))
  (at level 200, x ident, right associativity) : type_scope.

Example exists_ex_1: exists n, n + (n * n) = 6.
Proof. apply ex_intro with 2. reflexivity. Qed.

Example exists_ex_2: exists n, n + (n * n) = 6.
Proof.
  exists 2. (* equivalent to: intros. constructor 1 with 2. *)
  reflexivity.
Qed.

Theorem exists_ex_3: forall n,
  (exists m, n = 4 + m) -> (exists o, n = 2 + o).
Proof.
  intros. inversion H as [m Pm].
  exists (2 + m). apply Pm.
Qed.

Lemma exists_ex_4: exists n:nat, even n /\ beautiful n.
Proof.
  exists 8. split.
  Case "even". unfold even. reflexivity.
  Case "beautiful". apply bsum with (n:=3). apply b3. apply b5.
Qed.

(* Exercise: * optional *)
Eval compute in ex nat (fun n => beautiful (S n)).
(* In English: there is a number, n, that is beaufiful if one is added to it. *)

(* Exercise: * *)
Theorem dist_not_exists: forall (X:Type) (P:X -> Prop),
  (forall x, P x) -> ~ (exists x, ~ P x).
Proof.
  unfold not. intros X P H ex. inversion ex as [x Px].
  apply Px. apply H.
Qed.


(* Exercise: *** *)
Theorem not_exists_dist:
  excluded_middle ->
  forall (X:Type) (P:X -> Prop),
  ~ (exists x, ~ P x) -> (forall x, P x).
Proof.
  intros. unfold excluded_middle, not in *.
Abort.

(* Exercise: ** *)
Theorem dist_exists_or: forall (X:Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
  unfold iff. intros. split.
  Case "->".
    intros. inversion H. inversion H0.
    SCase "left".
      left. exists witness. assumption.
    SCase "right".
      right. exists witness. assumption.
  Case "<-".
    intros. inversion H.
    SCase "left".
      inversion H0. exists witness. left. assumption.
    SCase "right".
      inversion H0. exists witness. right. assumption.
Qed.


(* Evidence carrying booleans *)
Inductive sumbool (A B : Prop) : Set :=
| left : A -> sumbool A B
| right: B -> sumbool A B.
Notation "{ A } + { B }" := (sumbool A B) : type_scope.

Theorem eq_nat_dec: forall n m : nat, {n = m} + {n <> m}.
Proof.
  intros n. induction n.
  Case "n=0".
    intros m. destruct m.
    SCase "0". left. reflexivity.
    SCase "S". right. unfold not. intros. inversion H.
  Case "S".
    intros m. destruct m.
    SCase "0". right. unfold not. intros. inversion H.
    SCase "S". destruct IHn with (m:=m) as [eq | neq].
      SSCase "left".
        left. apply f_equal. assumption.
      SSCase "right".
        right. unfold not. intros. inversion H. unfold not in *. apply neq. assumption.
Defined.

Print eq_nat_dec.
Extraction eq_nat_dec. (* eq_nat_dec ends in defined so that the theorem has
                          computational value
                       *)


Definition override' {X:Type} (f:nat -> X) (k:nat) (x:X) : nat -> X :=
  fun (k':nat) => if eq_nat_dec k k' then x else f k'.

Theorem override_same': forall (X:Type) x1 k1 k2 (f:nat -> X),
  f k1 = x1 -> (override' f k1 x1) k2 = f k2.
Proof.
  intros. unfold override'. destruct (eq_nat_dec k1 k2).
  Case "left". rewrite <- e. symmetry. apply H.
  Case "right". reflexivity.
Qed.

(* Exercise: * *)
Theorem override_shadow': forall (X:Type) x1 x2 k1 k2 (f:nat -> X),
  (override' (override' f k1 x2) k1 x1) k2 = (override' f k1 x1) k2.
Proof.
  unfold override'. intros. destruct (eq_nat_dec k1 k2).
  Case "left". reflexivity.
  Case "right". reflexivity.
Qed.


(* Additional exercises *)

(* Exercise: **** advanced *)
Inductive appears_in {X:Type} (a:X) : list X -> Prop :=
| ai_here : forall l, appears_in a (a::l)
| ai_later : forall b l, appears_in a l -> appears_in a (b::l).


(* Exercise: *** *)
Inductive all {X:Type} (P:X -> Prop) : list X -> Prop :=
| nil  : all P []
| cons : forall {l:list X} (x:X) (xs:all P l), P x -> all P (x :: l).

Check nil.
Check cons.
Check cons even 4.
Check cons even 3.
Check even. Print even.
Definition t := nil even. Check t.
Definition t2 := cons even 2 t eq_refl. Check t2.
Definition t3 := cons even 4 t2 eq_refl. Check t3.
Definition t4 := cons even 6 t3 eq_refl. Check t4.
(* Definition t5 := cons even 7 t4 eq_refl. *)

(* important properties not visible in spec of [all]: forallb has a *decidable*
   test : X -> bool.
   [all] only requires a test : X -> Prop
*)

(* Exercise: *** *)
Inductive nostutter: list nat -> Prop :=
| nll : nostutter []
| sgl : forall x : nat, nostutter [x]
| nxt : forall (x y : nat) (p:x <> y) (xs:list nat), nostutter (y::xs) -> nostutter (x::y::xs).
(* 3 cases? gads *)

Example test_nostutter_1: nostutter [3;1;4;1;5;6].
Proof. repeat constructor; apply beq_nat_false; auto. Qed.

Example test_nostutter_2: nostutter [].
Proof. constructor 1. Qed.

Example test_nostutter_3: nostutter [5].
Proof. constructor 2. Qed.

Example test_nostutter_4: not (nostutter [3;1;1;4]).
Proof.
  intro. repeat match goal with
             h: nostutter _ |- _ => inversion h; clear h; subst
         end. apply p0. reflexivity.
Qed.


(* Exercise: **** advanced *)
Lemma app_length: forall (X:Type) (l1 l2 : list X),
  length (l1 ++ l2) = length l1 + length l2.
Proof.
  intros. induction l1.
  Case "[]".
    reflexivity.
  Case "::".
    simpl. apply f_equal. apply IHl1.
Qed.

Lemma appears_in_app_split: forall (X:Type) (x:X) (l:list X),
  appears_in x l ->
  exists l1, exists l2, l = l1 ++ (x::l2).
Proof.
Admitted.