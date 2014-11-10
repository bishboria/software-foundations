(* Poly: Polymorphism and higher order functions *)

Require Import Basics.
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
Require Export List.

(* Polymorphism *)

(** Polymorphic lists **)
Inductive boollist : Type :=
  | bnil : boollist
  | bcons : bool -> boollist -> boollist.

Inductive list (X:Type) : Type :=
  | nil : list X
  | cons : X -> list X -> list X.


Check nil.
Check cons.
Check (cons nat 2 (cons nat 1 (nil nat))).
Check cons nat 2 (nil _).

Fixpoint length (X:Type) (l:list X) : nat :=
  match l with
    | nil => 0
    | cons h t => S (length X t)
  end.

Example test_length1: length nat (cons nat 1 (cons nat 2 (nil nat))) = 2.
Proof. reflexivity. Qed.

Example test_length2: length bool (cons bool true (nil bool)) = 1.
Proof. reflexivity. Qed.

Fixpoint app (X:Type) (l1 l2 : list X) : list X :=
  match l1 with
    | nil      => l2
    | cons h t => cons X h (app X t l2)
  end.

Fixpoint snoc (X:Type) (l:list X) (v:X) : list X :=
  match l with
    | nil      => cons X v (nil X)
    | cons h t => cons X h (snoc X t v)
  end.

Fixpoint rev (X:Type) (l:list X) : list X :=
  match l with
    | nil => nil X
    | cons h t => snoc X (rev X t) h
  end.

Example test_rev1: rev nat (cons nat 1 (cons nat 2 (nil nat))) =
                   (cons nat 2 (cons nat 1 (nil nat))).
Proof. reflexivity. Qed.

Example test_rev2: rev bool (nil bool) = nil bool.
Proof. reflexivity. Qed.


Module MumbleBaz. (* <- Really? *)
  (* Exercise: ** *)
  Inductive mumble : Type :=
    | a : mumble
    | b : mumble -> nat -> mumble
    | c : mumble.

  Inductive grumble (X:Type) : Type :=
    | d : mumble -> grumble X
    | e : X -> grumble X.

  (* Check d (b a 5) *)
  Check d mumble (b a 5).
  Check d bool (b a 5).
  Check e bool true.
  Check e mumble (b c 0).
  (* Check e bool (b c 0) *)
  Check c.

  (* Exercise: ** *)
  Inductive baz : Type :=
    | x : baz -> baz
    | y : baz -> bool -> baz.
  (* 2 constructors, but infinite values. CoInductive instead of this?
     The constructors are not strictly positive... *)
End MumbleBaz.

(** Type annotation interface **)
Fixpoint app' X l1 l2 : list X :=
  match l1 with
    | nil => l2
    | cons h t => cons X h (app' X t l2)
  end.

Check app'.
Check app.

(* playing *)
Inductive Vec (X:Type) : nat -> Type :=
  | vnil  : Vec X O
  | vcons : forall n : nat, X -> Vec X n -> Vec X (S n).
(* end playing *)

(** Type argument synthesis **)

Fixpoint length' (X:Type) (l:list X) : nat :=
  match l with
    | nil => 0
    | cons h t => S (length' _ t)
  end.

(** Implicit Arguments **)
Arguments nil {X}.
Arguments cons {X} _ _.
Arguments length {X} l.
Arguments app {X} l1 l2.
Arguments rev {X} l.
Arguments snoc {X} l v.

Check cons 2 (cons 1 nil).

Fixpoint length'' {X:Type} (l:list X) : nat :=
  match l with
    | nil      => 0
    | cons h t => S (length'' t)
  end.

(* Definition mynil : nil. Missing type information... *)
Definition mynil  : list nat := nil.
Definition ymnil' := @nil nat.
Check @nil. (* force implicit arguments to be explicit *)

Notation "x :: y" := (cons x y) (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y) (at level 60, right associativity).

Check [1;2;3].
Check ([3;4] ++ nil).


(* Exercise: ** optional *)
Fixpoint repeat {X:Type} (n:X) (count:nat) : list X :=
  match count with
    | 0    => []
    | S c' => n :: repeat n c'
  end.


Example test_repeat1: repeat true 2 = [true;true].
Proof. reflexivity. Qed.

Theorem nil_app: forall (X:Type) (l:list X),
  app [] l = l.
Proof. reflexivity. Qed.

Theorem rev_snoc: forall (X:Type) (v:X) (s:list X),
  rev (snoc s v) = v :: (rev s).
Proof.
  intros. induction s.
  Case "s=[]".
    reflexivity.
  Case "s=::".
    simpl. rewrite IHs. reflexivity.
Qed.

Theorem rev_involutive: forall (X:Type) (l:list X),
  rev (rev l) = l.
Proof.
  intros. induction l.
  Case "l=[]".
    reflexivity.
  Case "l=::".
    simpl. rewrite rev_snoc. rewrite IHl. reflexivity.
Qed.

Theorem snoc_with_append: forall (X:Type) (l1 l2 : list X) (v:X),
  snoc (l1 ++ l2) v = l1 ++ (snoc l2 v).
Proof.
  intros. induction l1.
  Case "l=[]".
    reflexivity.
  Case "l=::".
    simpl. rewrite IHl1. reflexivity.
Qed.


(** Polymorphic pairs **)
Inductive prod (X Y : Type) : Type :=
  pair : X -> Y -> prod X Y.

Arguments pair {X} {Y} _ _.
Notation "( x , y )" := (pair x y).
Notation "X * Y" := (prod X Y) : type_scope. (* type_scope make sure * doesn't get confused about multplication and prod type *)

Definition fst {X Y : Type} (p:X*Y) : X :=
  match p with (x,y) => x end.

Definition snd {X Y : Type} (p:X*Y) : Y :=
  match p with (x,y) => y end.

Fixpoint combine {X Y : Type} (lx:list X) (ly:list Y) : list (X*Y) :=
  match lx, ly with
    | [], _            => []
    | _, []            => []
    | x :: xs, y :: ys => (x,y) :: combine xs ys
  end.

(* Exercise: * optional *)
(* Answer: combine : forall (X Y : Type), list X -> list Y -> list (X*Y). *)
Check @combine.
(* Answer: combine [1;2] [false;false;true;true] => [(1,false);(2,false)] : list (nat * bool) *)
Eval compute in combine [1;2] [false;false;true;true].


(* Exercise: ** *)
Fixpoint split {X Y : Type} (l:list (X*Y)) : (list X) * (list Y) :=
  match l with
    | []            => ([],[])
    | (x,y) :: rest => let (xs, ys) := split rest
                       in  (x :: xs, y :: ys)
  end.

Example test_split: split [(1,false);(2,false)] = ([1;2],[false;false]).
Proof. reflexivity. Qed.


(** Polymorphic options **)
Inductive option (X:Type) : Type :=
  | none : option X
  | some : X -> option X.

Arguments some {X} _.
Arguments none {X}.

Fixpoint index {X:Type} (n:nat) (l:list X) : option X :=
  match l with
    | []     => none
    | h :: t => if beq_nat n 0 then some h else index (pred n) t
  end.

Example test_index1: index 0 [4;5;6;7] = some 4.
Proof. reflexivity. Qed.

Example test_index2: index 1 [[1];[2]] = some [2].
Proof. reflexivity. Qed.

Example test_index3: index 2 [true] = none.
Proof. reflexivity. Qed.

(* Exercise: * optional *)
Definition hd_opt {X:Type} (l:list X) : option X :=
  match l with
    | []     => none
    | h :: _ => some h
  end.

Check hd_opt.
Check @hd_opt.

Example test_hd_opt1: hd_opt [1;2] = some 1.
Proof. reflexivity. Qed.

Example test_hd_opt2: hd_opt [[1];[2]] = some [1].
Proof. reflexivity. Qed.



(* Functions as data *)

(** Higher order functions **)
Definition doit3times {X:Type} (f:X->X) (n:X) : X :=
  f (f (f n)).

Check @doit3times.

Example test_doit3times1: doit3times minustwo 9 = 3.
Proof. reflexivity. Qed.

Example test_doit3times2: doit3times negb true = false.
Proof. reflexivity. Qed.

(** Partial application **)
Check plus.

Definition plus3 := plus 3.
Check plus3.

Example test_plus31: plus3 4 = 7.
Proof. reflexivity. Qed.

Example test_plus32: doit3times plus3 0 = 9.
Proof. reflexivity. Qed.

Example test_plus33: doit3times (plus 3) 0 = 9.
Proof. reflexivity. Qed.


(** Digression: Currying **)

(* Exercise: ** advanced *)
Definition prod_curry {X Y Z : Type} (f : X * Y -> Z) (x:X) (y:Y) : Z := f (x,y).

Definition prod_uncurry {X Y Z : Type} (f : X -> Y -> Z) (p:X*Y) : Z :=
  f (fst p) (snd p).

(* @prod_curry: forall X Y Z : Type, (X*Y -> Z) -> X -> Y -> Z *)
Check @prod_curry.

(* @prod_uncurry: forall X Y Z : Type, (X -> Y -> Z) -> X*Y -> Z *)
Check @prod_uncurry.

Theorem uncurry_curry: forall (X Y Z : Type) (f: X -> Y -> Z) (x:X) (y:Y),
  prod_curry (prod_uncurry f) x y = f x y.
Proof.
  reflexivity.
Qed.

Theorem curry_uncurry: forall (X Y Z : Type) (f:X*Y -> Z) (p:X*Y),
  prod_uncurry (prod_curry f) p = f p.
Proof.
  intros. destruct p. reflexivity.
Qed.


(** Filter **)
Fixpoint filter {X:Type} (f:X->bool) (l:list X) : list X :=
  match l with
    | []     => []
    | h :: t => if f h then
                  h :: (filter f t)
                else
                  filter f t
  end.

Example test_filter1: filter evenb [1;2;3;4] = [2;4].
Proof. reflexivity. Qed.

Definition length_is_1 {X:Type} (l:list X) : bool :=
  beq_nat (length l) 1.

Example test_filter2:
  filter length_is_1 [[1;2];[3];[4];[5;6;7];[];[8]] = [[3];[4];[8]].
Proof. reflexivity. Qed.

Definition countoddmembers' (l:list nat) : nat :=
  length (filter oddb l).

Example test_countoddmembers'1: countoddmembers' [1;0;3;1;4;5] = 4.
Proof. reflexivity. Qed.

Example test_countoddmembers'2: countoddmembers' [0;2;4] = 0.
Proof. reflexivity. Qed.

Example test_countoddmembers'3: countoddmembers' nil = 0.
Proof. reflexivity. Qed.


Example test_anon_fun': doit3times (fun n => n*n) 2 = 256.
Proof. reflexivity. Qed.

Example test_filter2': filter (fun l => beq_nat (length l) 1)
                              [[1;2];[3];[4];[5;6;7];[];[8]]
                       = [[3];[4];[8]].
Proof. reflexivity. Qed.

(* Exercise: ** *)
Definition filter_even_gt7 (l:list nat) : list nat :=
  filter (fun n => blt_nat 7 n) l.

Example test_filter_even_gt7_1:
  filter_even_gt7 [1;2;6;9;10;3;12;8] = [9;10;12;8].
Proof. reflexivity. Qed.

Example test_filter_even_gt7_2:
  filter_even_gt7 [5;2;6;1;2;7] = [].
Proof. reflexivity. Qed.

(* Exercise: *** *)
Definition partition {X:Type} (f:X->bool) (l:list X) : (list X)*(list X) :=
  (filter f l, filter (fun n => negb (f n)) l).

Example test_partition1: partition oddb [1;2;3;4;5] = ([1;3;5],[2;4]).
Proof. reflexivity. Qed.

Example test_partition2: partition (fun x => false) [5;9;0] = ([], [5;9;0]).
Proof. reflexivity. Qed.


(** Map **)
Fixpoint map {X Y : Type} (f:X->Y) (l:list X) : list Y :=
  match l with
    | []     => []
    | h :: t => f h :: map f t
  end.

Example test_map1: map (plus 3) [2;0;2] = [5;3;5].
Proof. reflexivity. Qed.

Example test_map2: map oddb [2;1;2;5] = [false; true; false; true].
Proof. reflexivity. Qed.

Example test_map3: map (fun n => [evenb n; oddb n]) [2;1;2;5] =
                   [[true;false];[false;true];[true;false];[false;true]].
Proof. reflexivity. Qed.


(** Map for options **)

(* Exercise: *** *)
Check @snoc.
Theorem map_snoc: forall (X Y : Type) (f:X->Y) (l:list X) (x:X),
  map f (snoc l x) = snoc (map f l) (f x).
Proof.
  intros. induction l.
  Case "l=[]".
    reflexivity.
  Case "l=::".
    simpl. rewrite IHl. reflexivity.
Qed.

Theorem map_rev: forall (X Y : Type) (f:X->Y) (l:list X),
  map f (rev l) = rev (map f l).
Proof.
  intros. induction l.
  Case "l=[]".
    reflexivity.
  Case "l=::".
    simpl. rewrite map_snoc. rewrite IHl. reflexivity.
Qed.

(* Exercise: ** *)
Fixpoint flat_map {X Y : Type} (f:X->list Y) (l:list X) : list Y :=
  match l with
    | [] => []
    | h :: t => (f h) ++ (flat_map f t)
  end.

Example test_flat_map1: flat_map (fun n => [n;n;n]) [1;5;4] = [1;1;1;5;5;5;4;4;4].
Proof. reflexivity. Qed.

Definition option_map {X Y : Type} (f:X->Y) (ox:option X) : option Y :=
  match ox with
    | none => none
    | some x => some (f x)
  end.

(* Exercise: ** *)
Fixpoint map' (X Y : Type) (f:X->Y) (l:list X) : list Y :=
  match l with
    | []     => []
    | h :: t => cons (f h) (map' X Y f t)
  end.

Fixpoint filter' (X:Type) (f:X->bool) (l:list X) : list X :=
  match l with
    | []     => []
    | h :: t => if f h then cons h (filter' X f t) else filter' X f t
  end.


(** Fold **)
Fixpoint fold {X Y : Type} (f:X->Y->Y) (b:Y) (l:list X) : Y :=
  match l with
    | []     => b
    | h :: t => f h (fold f b t)
  end.

Check fold andb.

Example fold_example1: fold mult 1 [1;2;3;4] = 24.
Proof. reflexivity. Qed.

Example fold_example2: fold andb true [true;true;false;true] = false.
Proof. reflexivity. Qed.

Example fold_example3: fold app [] [[1];[];[2;3];[4]] = [1;2;3;4].
Proof. reflexivity. Qed.

(* Exercise: * advanced *)
(** It's useful for f to be X -> Y -> Y, for instance, creating a show string
    for items (integers, say) to be printed **)


(** Functions for constructing functions **)
Definition constfun {X:Type} (x:X) : nat -> X :=
  fun (_:nat) => x.

Definition ftrue := constfun true.

Example constfun_1: ftrue 0 = true. reflexivity. Qed.
Example constfun_2: (constfun 5) 99 = 5. reflexivity. Qed.

Definition override {X:Type} (f:nat->X) (k:nat) (x:X) : nat -> X :=
  fun (k':nat) => if beq_nat k k' then x  else f k'.

Definition fmostlytrue := override (override ftrue 1 false) 3 false.

Example override_1: fmostlytrue 0 = true. reflexivity. Qed.
Example override_2: fmostlytrue 1 = false. reflexivity. Qed.
Example override_3: fmostlytrue 2 = true. reflexivity. Qed.
Example override_4: fmostlytrue 3 = false. reflexivity. Qed.

(* Exercise: * *)
Theorem override_example : forall b:bool,
  (override (constfun b) 3 true) 2 = b.
Proof. reflexivity. Qed.


(* [unfold] tactic *)
Theorem unfold_ex_bad: forall m n,
  3 + n = m -> plus3 n + 1 = m + 1.
Proof.
  intros.
  (* Can't do [rewrite H] yet, as Coq doesn't auto expand plus3 to 3+n *)
Abort.

Theorem unfold_ex: forall m n,
  3 + n = m -> plus3 n + 1 = m + 1.
Proof.
  intros. unfold plus3. rewrite H. reflexivity.
Qed.


Theorem beq_nat_refl : forall n : nat,
  true = beq_nat n n.
Proof.
  intros. induction n.
  Case "n=0".
    reflexivity.
  Case "n=S".
    simpl. rewrite IHn. reflexivity.
Qed.

Theorem override_eq: forall (X:Type) x k (f:nat->X),
  (override f k x) k = x.
Proof.
  intros. unfold override. rewrite <- beq_nat_refl. reflexivity.
Qed.

(* Exercise: ** *)
Definition fold_length {X:Type} (l:list X) : nat :=
  fold (fun _ n => S n) 0 l.

Example test_fold_length1: fold_length [4;7;0] = 3. reflexivity. Qed.

Theorem fold_length_correct : forall (X:Type) (l:list X),
  fold_length l = length l.
Proof.
  intros. induction l.
  Case "l=[]".
    reflexivity.
  Case "l=::".
    simpl. rewrite <- IHl. reflexivity.
Qed.


(* Exercise: *** *)
Definition fold_map {X Y : Type} (f:X->Y) (l:list X) : list Y :=
  fold (fun x xs => f x :: xs) [] l.

Theorem fold_map_map: forall (X Y : Type) (f:X->Y) (l:list X),
  fold_map f l = map f l.
Proof.
  intros. induction l.
  Case "l=[]".
    reflexivity.
  Case "l=::".
    simpl. rewrite <- IHl. reflexivity.
Qed.