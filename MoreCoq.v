(* Chapter 5 *)


Require Import Basics Induction.
Require Export Poly.

(* the [apply] tactic *)

Theorem silly1 : forall n m o p : nat,
  n = m -> [n;o] = [n;p] -> [n;o] = [m;p].
Proof.
  intros n m o p eq1 eq2.
  rewrite <- eq1. apply eq2. (* apply eq2. = rewrite eq2. reflexivity. *)
Qed.

Theorem silly2 : forall n m o p : nat,
  n = m ->
  (forall q r : nat, q = r -> [q;o] = [r;p]) ->
  [n;o] = [m;p].
Proof.
  intros n m o p eq1 eq2.
  apply eq2. apply eq1.
Qed.

Theorem silly2a : forall n m : nat,
  (n,n) = (m,m) ->
  (forall q r : nat, (q,q) = (r,r) -> [q] = [r]) ->
  [n] = [m].
Proof.
  intros n m eq1 eq2.
  apply eq2. (* conclusion of eq2 matches goal *)
  apply eq1. (* eq1 matches goal *)
Qed.

Theorem silly_ex :
  (forall n, evenb n = true -> oddb (S n) = true) ->
  evenb 3 = true -> oddb 4 = true.
Proof.
  intros.
  apply H. apply H0.
Qed.

Theorem silly3 : forall n : nat,
  true = beq_nat n 5 ->
  beq_nat (S (S n)) 7 = true.
Proof.
  intros.
  simpl.
  (* apply doesn't work directly as LHS and RHS are swapped *)
  symmetry. (* swap sides of = *)
  apply H.  (* now apply works *)
Qed.

(* Exercise: *** *)
Theorem rev_exercise : forall l l' : list nat,
  l = rev l' -> l' = rev l.
Proof.
  intros.
  SearchAbout rev.
  rewrite H. symmetry. apply rev_involutive.
Qed.


(* Apply... with...  tactic *)
Example trans_eq_ex: forall a b c d e f : nat,
  [a;b] = [c;d] ->
  [c;d] = [e;f] ->
  [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  rewrite eq1. rewrite eq2. reflexivity.
Qed.

Theorem trans_eq : forall (X:Type) (n m o : X),
  n = m -> m = o -> n = o.
Proof.
  intros X n m o eq1 eq2.
  rewrite eq1. rewrite eq2. reflexivity.
Qed.

Example trans_eq_ex' : forall a b c d e f : nat,
  [a;b] = [c;d] ->
  [c;d] = [e;f] ->
  [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  apply trans_eq with (m:=[c;d]). apply eq1. apply eq2.
Qed.


(* Exercise: *** *)
Example trans_eq_exercise : forall n m o p : nat,
  m = (minustwo o) ->
  (n + p) = m ->
  (n + p) = (minustwo o).
Proof.
  intros.
  apply trans_eq with (m:=minustwo o).
  rewrite H0. apply H. reflexivity.
Qed.


(* the [inversion] tactic *)
Theorem eq_add_S : forall n m : nat,
  S n = S m -> n = m.
Proof.
  intros.
  inversion H. reflexivity.
Qed.

Theorem silly4 : forall n m : nat,
  [n] = [m] ->
  n = m.
Proof.
  intros.
  inversion H. reflexivity.
Qed.

Theorem silly5 : forall n m o : nat,
  [n;m] = [o;o] ->
  [n] = [m].
Proof.
  intros.
  inversion H. reflexivity.
Qed.


(* Exercise: * *)
Example sillyex1 : forall (X:Type) (x y z : X) (l j : list X),
  x :: y :: l = z :: j ->
  y :: l = x :: j ->
  x = y.
Proof.
  intros X x y z l j eq1 eq2.
  inversion eq2. reflexivity.
Qed.

Theorem silly6 : forall n : nat,
  S n = 0 ->
  2 + 2 = 5.
Proof.
  intros n contra.
  inversion contra.
Qed.

Theorem silly7 : forall n m : nat,
  false = true ->
  [n] = [m].
Proof.
  intros n m contra.
  inversion contra.
Qed.

(* Exercise: * *)
Example sillyex2 : forall (X:Type) (x y z : X) (l j : list X),
  x :: y :: l = [] ->
  y :: l = z :: j ->
  x = z.
Proof.
  intros.
  inversion H.
Qed.

Theorem f_equal : forall (A B : Type) (f : A -> B) (x y : A),
  x = y -> f x = f y.
Proof.
  intros.
  rewrite H. reflexivity.
Qed.

(* Exercise: ** *)
Theorem beq_nat_0_l : forall n,
  beq_nat 0 n = true -> n = 0.
Proof.
  intros.
  destruct n. reflexivity. inversion H.
Qed.

(* Exercise: ** *)
Theorem beq_nat_0_r : forall n,
  beq_nat n 0 = true -> n = 0.
Proof.
  intros.
  destruct n. reflexivity. inversion H.
Qed.



(* using tactics on hypotheses *)
Theorem S_inj : forall (n m : nat) (b:bool),
  beq_nat (S n) (S m) = b ->
  beq_nat n m = b.
Proof.
  intros.
  simpl in H. apply H.
Qed.

Theorem silly3' : forall n : nat,
  (beq_nat n 5 = true -> beq_nat (S (S n)) 7 = true) ->
  true = beq_nat n 5 ->
  true = beq_nat (S (S n)) 7.
Proof.
  intros n eq H.
  symmetry in H. apply eq in H. symmetry. apply H.
Qed.


(* Exercise: *** *)
Theorem plus_n_n_injective : forall n m,
  n + n = m + m ->
  n = m.
Proof.
  intros n. induction n.
  Case "n=0".
    intros. destruct m. reflexivity. inversion H.
  Case "n=S".
    intros. destruct m. inversion H. simpl in H.
    (* below: getting the expression towards a canonical form before doing
       inversion? *)
    rewrite <- plus_n_Sm in H.
    rewrite <- plus_n_Sm in H.
    inversion H. apply IHn in H1. rewrite H1. reflexivity.
Qed.


(* varying the induction hypothesis *)
Theorem double_injective_FAILED: forall n m,
  double n = double m -> n = m.
Proof.
  intros n m. induction n.
  Case "n=0".
    simpl. intros eq. destruct m.
    SCase "m=0". reflexivity.
    SCase "m=S". inversion eq.
  Case "n=S".
    intros eq. destruct m.
    SCase "m=0". inversion eq.
    SCase "m=S". simpl in eq.
    (* Stuck. Extra S in IHn *)
    Abort.

Theorem double_injective: forall n m,
  double n = double m -> n = m.
Proof.
  intros n. induction n.
  Case "n=0".
    simpl. intros. destruct m.
    SCase "m=0". reflexivity.
    SCase "m=S". inversion H.
  Case "n=S".
    intros. destruct m.
    SCase "m=0". inversion H.
    SCase "m=S". apply f_equal. apply IHn. inversion H. reflexivity.
Qed.


(* Exercise: ** *)
Theorem beq_nat_true: forall n m,
  beq_nat n m = true -> n = m.
Proof.
  intros n. induction n.
  Case "n=0".
    intros. destruct m.
    SCase "m=0". reflexivity.
    SCase "m=S". inversion H.
  Case "n=S".
    intros. destruct m.
    SCase "m=0". inversion H.
    SCase "m=S". simpl in H. apply f_equal. apply IHn in H. apply H.
Qed.


Theorem double_injective_take2_failed: forall n m,
  double n = double m -> n = m.
Proof.
  intros n m. induction m.
  Case "m=0". simpl. intros eq. destruct n.
    SCase "n=0". reflexivity.
    SCase "n=S". inversion eq.
  Case "m=S". intros eq. destruct n.
    SCase "n=0". inversion eq.
    SCase "n=S". apply f_equal. rewrite eq in IHm. inversion eq. (* stuck *)
Abort.


Theorem double_injective_take2: forall n m,
  double n = double m -> n = m.
Proof.
  intros n m.
  generalize dependent n. (* put n back into the goal, leave m in the context *)
  induction m.
  Case "m=0". intros n eq. destruct n.
    SCase "n=0". reflexivity.
    SCase "n=S". inversion eq.
  Case "m=S". intros n eq. destruct n.
    SCase "n=0". inversion eq.
    SCase "n=S". apply f_equal. apply IHm. inversion eq. reflexivity.
Qed.


Theorem length_snoc' : forall (X:Type) (v:X) (l:list X) (n:nat),
  length l = n ->
  length (snoc l v) = S n.
Proof.
  intros X v l. induction l.
  Case "l=[]".
    intros. rewrite <- H. reflexivity.
  Case "l=::".
    intros. simpl. destruct n.
    SCase "n=0". inversion H.
    SCase "n=S". apply f_equal. apply IHl. inversion H. reflexivity.
Qed.


Theorem length_snoc_bad: forall (X:Type) (v:X) (l:list X) (n:nat),
  length l = n -> length (snoc l v) = S n.
Proof.
  intros X v l n eq. induction l.
  Case "l=[]". rewrite <- eq. reflexivity.
  Case "l=::". simpl. destruct n.
    SCase "n=0". inversion eq.
    SCase "n=S". apply f_equal. (* Can't apply IHl *)
Abort.


(* Exercise: *** *)
Theorem index_after_last: forall (n:nat) (X:Type) (l:list X),
  length l = n -> index n l = none.
Proof.
  intros. generalize dependent n.
  induction l.
  Case "l=[]". destruct n.
    SCase "n=0". reflexivity.
    SCase "n=S". intros. inversion H.
  Case "l=::". destruct n.
    SCase "n=0". intros. inversion H.
    SCase "n=S". intros. simpl. apply IHl. inversion H. reflexivity.
Qed.

(* Exercise: *** *)
Theorem length_snoc''': forall (n:nat) (X:Type) (v:X) (l:list X),
  length l = n -> length (snoc l v) = S n.
Proof.
  intros. generalize dependent n. induction l.
  Case "l=[]". destruct n.
    SCase "n=0". reflexivity.
    SCase "n=S". intros. inversion H.
  Case "l=::". destruct n.
    SCase "n=0". intros. inversion H.
    SCase "n=S". intros. simpl. apply f_equal. apply IHl. inversion H. reflexivity.
Qed.


(* Exercise: *** *)
Theorem app_length_cons: forall (X:Type) (l1 l2 : list X) (x:X) (n:nat),
  length (l1 ++ (x :: l2)) = n ->
  S (length (l1 ++ l2)) = n.
Proof.
  intros. generalize dependent n. induction l1.
  Case "l=[]". destruct n.
    SCase "n=0". intros. inversion H.
    SCase "n=S". intros. apply f_equal. simpl in H. inversion H. reflexivity.
  Case "l=::". destruct n.
    SCase "n=0". intros. inversion H.
    SCase "n=S". intros. apply f_equal. simpl. apply IHl1. simpl in H. inversion H. reflexivity.
Qed.




(* Exercise: **** *)
Lemma move_S: forall (X:Type) (x:X) (n:nat) (l1 l2 : list X),
  S (length (l1 ++ l2)) = n -> length (l1 ++ x :: l2) = n.
Proof.
  intros. generalize dependent n. generalize dependent l2. induction l1.
  Case "l1=[]".
    intros. simpl. simpl in H. apply H.
  Case "l1=::".
    intros. simpl. simpl in H. destruct n.
    SCase "n=0". inversion H.
    SCase "n=S". apply f_equal. apply IHl1. inversion H. reflexivity.
Qed.

Theorem app_length_twice: forall (X:Type) (n:nat) (l:list X),
  length l = n -> length (l ++ l) = n + n.
Proof.
  intros. generalize dependent n. induction l.
  Case "l=[]".
    simpl. intros. inversion H. reflexivity.
  Case "l=::".
    simpl. intros. destruct n.
    SCase "n=0". inversion H.
    SCase "n=S".
      simpl. apply f_equal. rewrite <- plus_n_Sm. inversion H. apply move_S.
      apply f_equal. rewrite H1. apply IHl. apply H1.
      (* Or: *)
      (* simpl. inversion H. rewrite H1. rewrite <- plus_n_Sm. apply f_equal.
      apply move_S. apply f_equal. apply IHl. apply H1. *)
Qed.


(* Exercise: *** *)
Theorem double_induction: forall (P:nat -> nat -> Prop),
  P 0 0 ->
  (forall m, P m 0 -> P (S m) 0) ->
  (forall n, P 0 n -> P 0 (S n)) ->
  (forall m n, P m n -> P (S m) (S n)) ->
  forall m n, P m n.
Proof.
  intros. generalize dependent n. induction m.
  Case "m=0". intros. induction n.
    SCase "n=0". apply H.
    SCase "n=S". apply H1. apply IHn.
  Case "m=S". intros. induction n.
    SCase "n=0". apply H0. apply IHm.
    SCase "n=S". apply H2. apply IHm.
Qed.


(* Using [destruct] on compound expressions *)
Definition sillyfun (n:nat) : bool :=
  if beq_nat n 3 then
    false
  else if beq_nat n 5 then
    false
  else
    false.

Theorem sillyfun_false : forall (n:nat),
  sillyfun n = false.
Proof.
  intros. unfold sillyfun. destruct (beq_nat n 3).
  Case "n=3 false". reflexivity.
  Case "n=3 true". destruct (beq_nat n 5).
    SCase "n=5 false". reflexivity.
    SCase "n=5 true". reflexivity.
Qed.


(* Exercise: * *)
Theorem override_shadow: forall (X:Type) x1 x2 k1 k2 (f : nat -> X),
  (override (override f k1 x2) k1 x1) k2 = (override f k1 x1) k2.
Proof.
  intros. unfold override. destruct (beq_nat k1 k2).
  Case "true". reflexivity.
  Case "false". reflexivity.
Qed.

(* Exercise: *** *)
Theorem combine_split: forall X Y (l:list (X * Y)) l1 l2,
  split l = (l1, l2) -> combine l1 l2 = l.
Proof.
  intros. unfold split in H. unfold combine.
Abort.


Definition sillyfun1 (n:nat) : bool :=
  if beq_nat n 3 then
    true
  else if beq_nat n 5 then
    true
  else false.

Theorem sillyfun1_odd_failed: forall n : nat,
  sillyfun1 n = true -> oddb n = true.
Proof.
  intros. unfold sillyfun1 in H. destruct (beq_nat n 3).
  (* lost the information that n = 3 for beq_nat n 3 = true. *)
Abort.

Theorem sillyfun1_odd: forall n : nat,
  sillyfun1 n = true -> oddb n = true.
Proof.
  intros. unfold sillyfun1 in H.
  destruct (beq_nat n 3) eqn:bn3. (* remembers beq_nat n 3 in the context as bn3 *)
  Case "n=3 true".
    apply beq_nat_true in bn3. rewrite bn3. reflexivity.
  Case "n=3 false".
    destruct (beq_nat n 5) eqn:bn5. (* remember beq_nat n 5 in the context as bn5 *)
    SCase "n=5 true". apply beq_nat_true in bn5. rewrite bn5. reflexivity.
    SCase "n=5 false". inversion H.
Qed.



(* Exercise: ** *)
Theorem bool_fn_applied_thrice: forall (f:bool -> bool) (b:bool),
  f (f (f b)) = f b.
Proof.
  intros. destruct b. destruct (f true) eqn:ft.
  Case "ft=true". rewrite ft. apply ft.
  Case "ft=false". destruct (f false) eqn:ff.
    apply ft. apply ff.
  destruct (f false) eqn:ff.
  Case "ff=true". destruct (f true) eqn:ft.
    apply ft. apply ff. rewrite ff. apply ff.
Qed.


(* Exercise: ** *)
Theorem override_same: forall (X:Type) x1 k1 k2 (f:nat -> X),
  f k1 = x1 -> (override f k1 x1) k2 = f k2.
Proof.
  intros. unfold override. destruct (beq_nat k1 k2) eqn:be.
  Case "be=true".
    apply beq_nat_true in be. rewrite <- H. rewrite be. reflexivity.
  Case "be=false".
    reflexivity.
Qed.


(* Additional exercises *)

(* Exercise: *** *)
Theorem beq_nat_sym: forall n m : nat,
  beq_nat n m = beq_nat m n.
Proof.
  intros. destruct (beq_nat n m) eqn:bnm.
  Case "bnm=true". apply beq_nat_true in bnm. rewrite bnm. apply beq_nat_refl.
  Case "bnm=false". destruct (beq_nat m n) eqn:bmn.
    SCase "bmn=true".
      rewrite <- bnm. apply beq_nat_true in bmn. rewrite bmn. symmetry.
      apply beq_nat_refl.
    SCase "bmn=false".
      reflexivity.
Qed.


(* Exercise: *** *)
Theorem beq_nat_trans: forall n m p,
  beq_nat n m = true ->
  beq_nat m p = true ->
  beq_nat n p = true.
Proof.
  intros. destruct (beq_nat n m) eqn:bnm.
  Case "bnm=t". apply beq_nat_true in bnm. rewrite <- bnm in H0. apply H0.
  Case "bnm=f". inversion H.
Qed.


(* Exercise: *** *)
Theorem override_permute: forall (X:Type) x1 x2 k1 k2 k3 (f:nat -> X),
  beq_nat k2 k1 = false ->
  (override (override f k2 x2) k1 x1) k3 = (override (override f k1 x1) k2 x2) k3.
Proof.
  intros. unfold override. destruct (beq_nat k1 k3) eqn:b13.
  Case "b13=t".
    apply beq_nat_true in b13. rewrite <- b13. rewrite H. reflexivity.
  Case "b13=f".
    reflexivity.
Qed.


(* Exercise: *** *)
Theorem filter_exercise: forall (X:Type) (test:X -> bool) (x:X) (l lf : list X),
  filter test l = x :: lf -> test x = true.
Proof.
  intros. destruct (test x) eqn:tx.
  Case "tx=t". reflexivity.
  Case "tx=f". unfold filter in H.
Abort.


Fixpoint forallb {X:Type} (f:X -> bool) (l:list X) : bool :=
  match l with
    | nil     => true
    | x :: xs => if f x then forallb f xs else false
  end.

Eval compute in forallb oddb [1;3;5;7;9] = true.
Eval compute in forallb negb [false;false] = true.
Eval compute in forallb evenb [0;2;4;5] = false.
Eval compute in forallb (beq_nat 5) [] = true.

Fixpoint existsb {X:Type} (f:X -> bool) (l:list X) : bool :=
  match l with
    | nil     => false
    | x :: xs => if f x then true else existsb f xs
  end.

Eval compute in existsb (beq_nat 5) [0;2;3;6] = false.
Eval compute in existsb (andb true) [true;true;false] = true.
Eval compute in existsb oddb [1;0;0;0;0;3] = true.
Eval compute in existsb evenb [] = false.

Definition existsb' {X:Type} (f:X->bool) (l:list X) := negb (forallb (fun n => negb (f n)) l).

Eval compute in existsb' (beq_nat 5) [0;2;3;6] = false.
Eval compute in existsb' (beq_nat 5) [0;2;4;5] = true.
Eval compute in existsb' (andb true) [true;true;false] = true.
Eval compute in existsb' oddb [1;0;0;0;0;3] = true.
Eval compute in existsb' evenb [] = false.

Theorem existsb_existsb'_eq: forall (X:Type) (f:X->bool) (l:list X),
  existsb f l = existsb' f l.
Proof.
  intros. induction l.
  Case "l=[]". reflexivity.
  Case "l=::".
    simpl. rewrite IHl. unfold existsb', forallb. destruct (f x); reflexivity.
Qed.