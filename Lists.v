(* Chapter 3 Lists *)


Require Export Induction.



Module NatList.

(* Pairs of numbers *)
  Inductive natprod : Type :=
    pair : nat -> nat -> natprod.

  Check pair 3 5.

  Definition fst (p:natprod) : nat :=
    match p with
      | pair x y => x
    end.

  Definition snd (p:natprod) : nat :=
    match p with
      | pair x y => y
    end.

  Eval compute in fst (pair 3 5).

  Notation "( x , y )" := (pair x y).

  Eval compute in fst (3, 5).

  Definition fst' (p:natprod) : nat :=
    match p with
      | (x,y) => x
    end.

  Definition snd' (p:natprod) : nat :=
    match p with
      | (x,y) => y
    end.

  Definition swap_pair (p:natprod) : natprod :=
    match p with
      | (x,y) => (y,x)
    end.

  Theorem surjective_pairing' : forall n m : nat,
    (n,m) = (fst (n,m), snd (n,m)).
  Proof.
    reflexivity.
  Qed.

  Theorem surjective_pairing_stuck : forall p : natprod,
    p = (fst p, snd p).
  Proof.
    simpl. (* Doesn't reduce anything *)
  Abort.

  Theorem surjective_pairing : forall p : natprod,
    p = (fst p, snd p).
  Proof.
    intros. destruct p. reflexivity.
  Qed.

  (* Exercise: * *)
  Theorem snd_fst_is_swap : forall p : natprod,
    (snd p, fst p) = swap_pair p.
  Proof.
    intros. destruct p. reflexivity.
  Qed.

  (* Exercise: * *)
  Theorem fst_swap_is_snd : forall p : natprod,
    fst (swap_pair p) = snd p.
  Proof.
    intros. destruct p. reflexivity.
  Qed.


(* List of Numbers *)

  Inductive natlist : Type :=
    | nil  : natlist
    | cons : nat -> natlist -> natlist.

  Definition mylist := cons 1 (cons 2 (cons 3 nil)).

  Notation "x :: l"         := (cons x l) (at level 60, right associativity).
  Notation "[]"             := nil.
  Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).
  (* lower level number -> higher binding precedence *)

  Fixpoint repeat (n count : nat) : natlist :=
    match count with
      | 0        => nil
      | S count' => n :: (repeat n count')
    end.

  Fixpoint length (l:natlist) : nat :=
    match l with
      | nil    => 0
      | h :: t => S (length t)
    end.

  Fixpoint app (l1 l2 : natlist) : natlist :=
    match l1 with
      | nil    => l2
      | h :: t => h :: app t l2
    end.

  Notation "x ++ y" := (app x y) (at level 60, right associativity).

  Example test_app1: [1;2;3] ++ [4;5] = [1;2;3;4;5].
  Proof. reflexivity. Qed.

  Example test_app2: nil ++ [4;5] = [4;5].
  Proof. reflexivity. Qed.

  Example test_app3: [1;2;3] ++ nil = [1;2;3].
  Proof. reflexivity. Qed.

  Definition hd (default:nat) (l:natlist) : nat :=
    match l with
      | nil    => default
      | h :: t => h
    end.

  Definition tl (l:natlist) : natlist :=
    match l with
      | nil    => nil
      | h :: t => t
    end.

  Example test_hd1: hd 0 [1;2;3] = 1.
  Proof. reflexivity. Qed.

  Example test_hd2: hd 0 [] = 0.
  Proof. reflexivity. Qed.

  Example test_tl: tl [1;2;3] = [2;3].
  Proof. reflexivity. Qed.

  (* Exercise: ** *)
  Fixpoint nonzeros (l:natlist) : natlist :=
    match l with
      | nil => nil
      | 0 :: t => nonzeros t
      | h :: t => h :: nonzeros t
    end.

  Example test_nonzeros: nonzeros [0;1;0;2;3;0;0] = [1;2;3].
  Proof. reflexivity. Qed.

  Fixpoint oddmembers (l:natlist) : natlist :=
    match l with
      | nil    => nil
      | h :: t => if oddb h then
                    h :: oddmembers t
                  else
                    oddmembers t
                  end.

  Example test_oddmembers: oddmembers [0;1;0;2;3;0;0] = [1;3].
  Proof. reflexivity. Qed.

  Definition countoddmembers (l:natlist) : nat :=
    length (oddmembers l).

  Example test_countoddmembers1: countoddmembers [1;0;3;1;4;5] = 4.
  Proof. reflexivity. Qed.

  Example test_countoddmembers2: countoddmembers [0;2;4] = 0.
  Proof. reflexivity. Qed.

  Example test_countoddmembers3: countoddmembers nil = 0.
  Proof. reflexivity. Qed.


  (* Exercise: *** *)
  Fixpoint alternate (l1 l2 : natlist) : natlist :=
    match l1, l2 with
      | nil, _ => l2
      | _, nil => l1
      | h1 :: t1, h2 :: t2 => h1 :: h2 :: alternate t1 t2
    end.

  Example test_alternate1: alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6].
  Proof. reflexivity. Qed.

  Example test_alternate2: alternate [1] [4;5;6] = [1;4;5;6].
  Proof. reflexivity. Qed.

  Example test_alternate3: alternate [1;2;3] [4] = [1;4;2;3].
  Proof. reflexivity. Qed.

  Example test_alternate4: alternate [] [20;30] = [20;30].
  Proof. reflexivity. Qed.


(* Bags via Lists *)

  Definition bag := natlist.

  (* Exercise: *** *)
  Fixpoint count (v:nat) (s:bag) : nat :=
    match s with
      | nil => 0
      | h :: t => if beq_nat h v then
                    1 + (count v t)
                  else
                    count v t
    end.

  Example test_count1: count 1 [1;2;3;1;4;1] = 3.
  Proof. reflexivity. Qed.

  Example test_count2: count 6 [1;2;3;1;4;1] = 0.
  Proof. reflexivity. Qed.


  Definition sum : bag -> bag -> bag := app.

  Example test_sum1: count 1 (sum [1;2;3] [1;4;1]) = 3.
  Proof. reflexivity. Qed.

  Definition add (v:nat) (s:bag) : bag := cons v s.

  Example test_add1: count 1 (add 1 [1;4;1]) = 3.
  Proof. reflexivity. Qed.

  Example test_add2: count 5 (add 1 [1;4;1]) = 0.
  Proof. reflexivity. Qed.

  Definition member (v:nat) (s:bag) : bool :=
    match count v s with
      | 0 => false
      | _ => true
    end.

  Example test_member1: member 1 [1;4;1] = true.
  Proof. reflexivity. Qed.

  Example test_member2: member 2 [1;4;1] = false.
  Proof. reflexivity. Qed.

  (* Exercise: *** optional *)
  Fixpoint remove_one (v:nat) (s:bag) : bag :=
    match s with
      | nil    => nil
      | h :: t => match beq_nat h v with
                    | true  => t
                    | false => h :: remove_one v t
                  end
    end.

  Example test_remove_one1: count 5 (remove_one 5 [2;1;5;4;1]) = 0.
  Proof. reflexivity. Qed.

  Example test_remove_one2: count 5 (remove_one 5 [2;1;4;1]) = 0.
  Proof. reflexivity. Qed.

  Example test_remove_one3: count 4 (remove_one 5 [2;1;4;5;1;4]) = 2.
  Proof. reflexivity. Qed.

  Example test_remove_one4: count 5 (remove_one 5 [2;1;5;4;5;1;4]) = 1.
  Proof. reflexivity. Qed.

  Fixpoint remove_all (v:nat) (s:bag) : bag :=
    match s with
      | nil    => nil
      | h :: t => match beq_nat h v with
                    | true  => remove_all v t
                    | false => h :: remove_all v t
                  end
    end.

  Example test_remove_all1: count 5 (remove_all 5 [2;1;5;4;1]) = 0.
  Proof. reflexivity. Qed.

  Example test_remove_all2: count 5 (remove_all 5 [2;1;4;1]) = 0.
  Proof. reflexivity. Qed.

  Example test_remove_all3: count 4 (remove_all 5 [2;1;4;5;1;4]) = 2.
  Proof. reflexivity. Qed.

  Example test_remove_all4: count 5 (remove_all 5 [2;1;5;4;5;1;4;5;1;4]) = 0.
  Proof. reflexivity. Qed.

  Fixpoint subset (s1 s2 : bag) : bool :=
    match s1 with
      | nil    => true
      | h :: t => match member h s2 with
                    | true  => subset t (remove_one h s2)
                    | false => false
                  end
    end.

  Example test_subset1: subset [1;2] [2;1;4;1] = true.
  Proof. reflexivity. Qed.

  Example test_subset2: subset [1;2;2] [2;1;4;1] = false.
  Proof. reflexivity. Qed.


  (* Exercise: *** Prove a theorem about bags using count and add *)
  (* TODO *)



(* Reasoning About Lists *)

  Theorem tl_length_pred: forall l : natlist,
    pred (length l) = length (tl l).
  Proof.
    intros. destruct l.
    Case "l=[]".
      reflexivity.
    Case "l=::".
      reflexivity.
  Qed.

  Theorem app_assoc: forall l1 l2 l3 : natlist,
    (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
  Proof.
    intros. induction l1.
    Case "l1 = []".
      reflexivity.
    Case "l1 = ::".
      simpl. rewrite IHl1. reflexivity.
  Qed.

  Theorem app_length : forall l1 l2 : natlist,
    length (l1 ++ l2) = (length l1) + length l2.
  Proof.
    intros. induction l1.
    Case "l=[]".
      reflexivity.
    Case "l=::".
      simpl. rewrite IHl1. reflexivity.
  Qed.

  (** Revering a list **)

  Fixpoint snoc (l:natlist) (v:nat) : natlist :=
    match l with
      | nil => [v]
      | h :: t => h :: (snoc t v)
    end.

  Fixpoint rev (l:natlist) : natlist :=
    match l with
      | nil    => nil
      | h :: t => snoc (rev t) h
    end.

  Example test_rev1: rev [1;2;3] = [3;2;1].
  Proof. reflexivity. Qed.

  Example test_rev2: rev nil = nil.
  Proof. reflexivity. Qed.

  (** Proofs about reverse **)
  Theorem rev_length_firsttry : forall l : natlist,
    length (rev l) = length l.
  Proof.
    intros. induction l.
    Case "l=[]".
      reflexivity.
    Case "l=::".
      simpl.
      rewrite <- IHl. (* only thing we can do... but now stuck *)
  Abort.

  Theorem length_snoc : forall n : nat, forall l : natlist,
    length (snoc l n) = S (length l).
  Proof.
    intros. induction l.
    Case "l=[]".
      reflexivity.
    Case "l=::".
      simpl. rewrite IHl. reflexivity.
  Qed.

  Theorem rev_length: forall l : natlist,
    length (rev l) = length l.
  Proof.
    intros. induction l.
    Case "l=[]".
      reflexivity.
    Case "l=::".
      simpl. rewrite length_snoc. rewrite IHl. reflexivity.
  Qed.


(* SearchAbout *)

  SearchAbout rev. (* lists things proven that contain the name [rev] *)


  (* Exercise: *** *)
  Theorem app_nil_end: forall l : natlist,
    l ++ [] = l.
  Proof.
    intros. induction l.
    Case "l=[]".
      reflexivity.
    Case "l=::".
      simpl. rewrite IHl. reflexivity.
  Qed.

  Theorem rev_snoc: forall n : nat, forall l : natlist,
    rev (snoc l n) = n :: rev l.
  Proof.
    intros. induction l.
    Case "l=[]".
      reflexivity.
    Case "l=::".
      simpl. rewrite IHl. reflexivity.
  Qed.

  Theorem rev_involutive: forall l : natlist,
    rev (rev l) = l.
  Proof.
    intros. induction l.
    Case "l=[]".
      reflexivity.
    Case "l=::".
      simpl. rewrite rev_snoc. rewrite IHl. reflexivity.
  Qed.


  Theorem app_assoc4: forall l1 l2 l3 l4 : natlist,
    l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
  Proof.
    intros. induction l1.
    Case "l=[]".
      simpl. rewrite app_assoc. reflexivity.
    Case "l=::".
      simpl. rewrite IHl1. reflexivity.
  Qed.

  Theorem snoc_append: forall (l:natlist) (n:nat),
    snoc l n = l ++ [n].
  Proof.
    intros. induction l.
    Case "l=[]".
      reflexivity.
    Case "l=::".
      simpl. rewrite IHl. reflexivity.
  Qed.

  Theorem distr_rev: forall l1 l2 : natlist,
    rev (l1 ++ l2) = (rev l2) ++ (rev l1).
  Proof.
    intros. induction l1.
    Case "l=[]".
      simpl. rewrite app_nil_end. reflexivity.
    Case "l=::".
      simpl. rewrite IHl1. rewrite snoc_append. rewrite snoc_append.
      rewrite app_assoc. reflexivity.
  Qed.

  Theorem nonzeros_app: forall l1 l2 : natlist,
    nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
  Proof.
    intros. induction l1.
    Case "l=[]".
      reflexivity.
    Case "l=::".
      induction n.
      SCase "n=O".
        simpl. rewrite IHl1. reflexivity.
      SCase "n=S".
        simpl. rewrite IHl1. reflexivity.
  Qed.

  (* Exercise: ** *)
  Fixpoint beq_natlist (l1 l2 : natlist) : bool :=
    match l1, l2 with
      | nil, nil       => true
      | h :: t, i :: u => match beq_nat h i with
                            | true  => beq_natlist t u
                            | false => false
                          end
      | _, _           => false
    end.

  Example test_beq_natlist1: beq_natlist nil nil = true.
  Proof. reflexivity. Qed.

  Example test_beq_natlist2: beq_natlist [1;2;3] [1;2;3] = true.
  Proof. reflexivity. Qed.

  Example test_beq_natlist3: beq_natlist [1;2;3] [1;2;4] = false.
  Proof. reflexivity. Qed.

  Theorem beq_natlist_refl: forall l : natlist,
    true = beq_natlist l l.
  Proof.
    intros. induction l.
    Case "l=[]".
      reflexivity.
    Case "l=::".
      simpl. rewrite <- beq_nat_refl. rewrite IHl. reflexivity.
  Qed.


  (* Exercise: ** list_design *)
  (* TODO *)

  (* Exercise: *** *)
  Theorem count_member_nonzero: forall s : bag,
    ble_nat 1 (count 1 (1 :: s)) = true.
  Proof. reflexivity. Qed.

  Theorem ble_n_Sn: forall n,
    ble_nat n (S n) = true.
  Proof.
    intros. induction n.
    Case "n=0".
      reflexivity.
    Case "n=S".
      simpl. rewrite IHn. reflexivity.
  Qed.

  Theorem remove_decreases_count: forall s : bag,
    ble_nat (count 0 (remove_one 0 s)) (count 0 s) = true.
  Proof.
    intros. induction s.
    Case "s=[]".
      reflexivity.
    Case "s=::".
      induction n.
      SCase "n=0".
        simpl. rewrite ble_n_Sn. reflexivity.
      SCase "n=S".
        simpl. rewrite IHs. reflexivity.
  Qed.


  (* Exercise: **** *)
  Theorem rev_injective: forall l1 l2 : natlist,
    rev l1 = rev l2 -> l1 = l2.
  Proof.
    intros.
    rewrite <- rev_involutive.
    rewrite <- H.
    rewrite rev_involutive.
    reflexivity.
  Qed.


(* Options *)

  Fixpoint index_bad (n:nat) (l:natlist) : nat :=
    match l with
      | nil    => 42 (* arbitrary *)
      | h :: t => match beq_nat n 0 with
                    | true  => h
                    | false => index_bad (pred n) t
                  end
    end.

  Inductive natoption : Type :=
    | some : nat -> natoption
    | none : natoption.

  Fixpoint index (n:nat) (l:natlist) : natoption :=
    match l with
      | nil    => none
      | h :: t => match beq_nat n 0 with
                    | true => some h
                    | false => index (pred n) t
                  end
    end.

  Example test_index1: index 0 [4;5;6;7] = some 4.
  Proof. reflexivity. Qed.

  Example test_index2: index 3 [4;5;6;7] = some 7.
  Proof. reflexivity. Qed.

  Example test_index3: index 10 [4;5;6;7] = none.
  Proof. reflexivity. Qed.


  (** using conditionals **)
  Fixpoint index' (n:nat) (l:natlist) : natoption :=
    match l with
      | nil    => none
      | h :: t => if beq_nat n 0 then some h else index' (pred n) t
    end.

  Definition option_elim (d:nat) (o:natoption) : nat :=
    match o with
      | some n => n
      | none   => d
    end.

  (* Exercise: ** *)
  Definition hd_opt (l:natlist) : natoption :=
    match l with
      | nil    => none
      | h :: _ => some h
    end.

  Example test_hd_opt1: hd_opt [] = none.
  Proof. reflexivity. Qed.

  Example test_hd_opt2: hd_opt [1] = some 1.
  Proof. reflexivity. Qed.

  Example test_hd_opt3: hd_opt [5;6] = some 5.
  Proof. reflexivity. Qed.

  (* Exercise: * optional *)
  Theorem option_elim_hd: forall (l:natlist) (default:nat),
    hd default l = option_elim default (hd_opt l).
  Proof.
    intros. destruct l.
    reflexivity. reflexivity.
  Qed.


(* Dictionaries *)

  Module Dictionary.

    Inductive dictionary : Type :=
      | empty  : dictionary
      | record : nat -> nat -> dictionary -> dictionary.

    Definition insert (key value : nat) (d : dictionary) : dictionary :=
      record key value d.

    Fixpoint find (key:nat) (d:dictionary) : natoption :=
      match d with
        | empty         => none
        | record k v d' => if   beq_nat key k
                           then some v
                           else find key d'
      end.

    (* Exercise: * *)
    Theorem dictionary_invariant1': forall (d:dictionary) (k v : nat),
      find k (insert k v d) = some v.
    Proof.
      intros. simpl.
      replace (beq_nat k k) with (true).
      reflexivity.
      Case "proof of replace". apply beq_nat_refl.
    Qed.

    (* exercise: * *)
    Theorem dictionary_invariant2' : forall (d:dictionary) (m n o : nat),
      beq_nat m n = false ->
      find m d = find m (insert n o d).
    Proof.
      intros. simpl.
      rewrite H. reflexivity.
    Qed.

  End Dictionary.
End NatList.