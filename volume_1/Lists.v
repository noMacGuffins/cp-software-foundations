From LF Require Export Induction.
Module NatList.

(* Pairs of Numbers *)
Inductive natprod : Type :=
  | pair (n1 n2 : nat).
  
Check (pair 3 5) : natprod.

Definition fst (p : natprod) : nat :=
  match p with
  | pair x y => x
  end.
Definition snd (p : natprod) : nat :=
  match p with
  | pair x y => y
  end.
Compute (fst (pair 3 5)).
(* ===> 3 *)

Notation "( x , y )" := (pair x y).

Compute (fst (3,5)).
Definition fst' (p : natprod) : nat :=
  match p with
  | (x,y) => x
  end.
Definition snd' (p : natprod) : nat :=
  match p with
  | (x,y) => y
  end.
Definition swap_pair (p : natprod) : natprod :=
  match p with
  | (x,y) => (y,x)
  end.

(* Do not confuse with multiple pattern syntax with no paranthesis *)
Fixpoint minus (n m : nat) : nat :=
    match n, m with
    | O   , _    => O
    | S _ , O    => n
    | S n', S m' => minus n' m'
    end.

(* simplication success *)
Theorem surjective_pairing' : forall (n m : nat),
  (n,m) = (fst (n,m), snd (n,m)).
Proof.
  reflexivity. Qed.

(* Doesn't reduce anything! *)
Theorem surjective_pairing_stuck : forall (p : natprod),
  p = (fst p, snd p).
Proof.
  simpl. 
Abort.

(* With destruct *)
Theorem surjective_pairing : forall (p : natprod),
  p = (fst p, snd p).
Proof.
  intros p. destruct p as [n m]. simpl. reflexivity. Qed.

(* Exercise: snd_fst_is_swap *)
Theorem snd_fst_is_swap : forall (p : natprod),
  (snd p, fst p) = swap_pair p.
Proof.
  intros p. destruct p as [n m]. simpl. reflexivity. Qed.
(* Exercise end *)

(* Exercise: fst_swap_is_snd *)
Theorem fst_swap_is_snd : forall (p : natprod),
  fst (swap_pair p) = snd p.
Proof.
  intros p. destruct p as [n m]. simpl. reflexivity. Qed.
(* Exercise end *)

(* Lists of Numbers *)

Inductive natlist : Type :=
  | nil
  | cons (n : nat) (l : natlist).

Definition mylist := cons 1 (cons 2 (cons 3 nil)).

Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

(* meaning of right associativity *)
Definition mylist1 := 1 :: (2 :: (3 :: nil)).
Definition mylist2 := 1 :: 2 :: 3 :: nil.
Definition mylist3 := [1;2;3].

(* meaning of level 60: compare with + infix notation *)
Notation "x + y" := (plus x y) (at level 50, left associativity).
(* 
the + operator will bind tighter than ::, 
so 1 + 2 :: [3] will be parsed, as we'd expect, 
as (1 + 2) :: [3] rather than 1 + (2 :: [3]) 
*)

Fixpoint repeat (n count : nat) : natlist :=
  match count with
  | O => nil
  | S count' => n :: (repeat n count')
  end.

Fixpoint length (l:natlist) : nat :=
  match l with
  | nil => O
  | h :: t => S (length t)
  end.


Fixpoint app (l1 l2 : natlist) : natlist :=
  match l1 with
  | nil => l2
  | h :: t => h :: (app t l2)
  end.

Notation "x ++ y" := (app x y)
                     (right associativity, at level 60).
Example test_app1: [1;2;3] ++ [4;5] = [1;2;3;4;5].
Proof. reflexivity. Qed.
Example test_app2: nil ++ [4;5] = [4;5].
Proof. reflexivity. Qed.
Example test_app3: [1;2;3] ++ nil = [1;2;3].
Proof. reflexivity. Qed.

Definition hd (default : nat) (l : natlist) : nat :=
  match l with
  | nil => default
  | h :: t => h
  end.
Definition tl (l : natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => t
  end.
Example test_hd1: hd 0 [1;2;3] = 1.
Proof. reflexivity. Qed.
Example test_hd2: hd 0 [] = 0.
Proof. reflexivity. Qed.
Example test_tl: tl [1;2;3] = [2;3].
Proof. reflexivity. Qed.


(* Exercise: list_funs *)

Fixpoint nonzeros (l:natlist) : natlist := 
    match l with
        | nil => nil
        | O :: t => nonzeros t
        | n :: t => n :: nonzeros t
    end.
Example test_nonzeros:
  nonzeros [0;1;0;2;3;0;0] = [1;2;3].
Proof. reflexivity. Qed.
Check odd.
Fixpoint oddmembers (l:natlist) : natlist :=
    match l with
        | nil => nil
        | h :: t => 
            match (odd h) with
                | false => oddmembers t
                | true => h :: oddmembers t
            end
    end.
Example test_oddmembers:
  oddmembers [0;1;0;2;3;0;0] = [1;3].
Proof. reflexivity. Qed.

Definition countoddmembers (l:natlist) : nat :=
  length (oddmembers l).

Example test_countoddmembers1:
  countoddmembers [1;0;3;1;4;5] = 4.
Proof. simpl. reflexivity. Qed.
Example test_countoddmembers2:
  countoddmembers [0;2;4] = 0.
  Proof. simpl. reflexivity. Qed.
Example test_countoddmembers3:
  countoddmembers nil = 0.
  Proof. simpl. reflexivity. Qed.

(* Exercise end *)

(* Exercise: alternate *)
Fixpoint alternate (l1 l2 : natlist) : natlist := 
  match l1, l2 with
    | h1 :: t1, h2 :: t2 => h1 :: h2 :: alternate t1 t2
    | l1, nil => l1
    | nil, l2 => l2
  end.
Example test_alternate1:
  alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6].
Proof. reflexivity. Qed.
Example test_alternate2:
  alternate [1] [4;5;6] = [1;4;5;6].
Proof. reflexivity. Qed.
Example test_alternate3:
  alternate [1;2;3] [4] = [1;4;2;3].
Proof. reflexivity. Qed.
Example test_alternate4:
  alternate [] [20;30] = [20;30].
Proof. reflexivity. Qed.
(* Exercise end *)


(* Bags via Lists *)
Definition bag := natlist.

(* Exercise: bag_functions *)
Fixpoint count (v : nat) (s : bag) : nat := 
  match s with
    | h :: t => if v =? h then S (count v t) else count v t
    | nil => O
  end.
Example test_count1: count 1 [1;2;3;1;4;1] = 3.
Proof. reflexivity. Qed.
Example test_count2: count 6 [1;2;3;1;4;1] = 0.
Proof. reflexivity. Qed.

Definition sum : bag -> bag -> bag := app.
Example test_sum1: count 1 (sum [1;2;3] [1;4;1]) = 3.
Proof. reflexivity. Qed.
Definition add (v : nat) (s : bag) : bag := cons v s.
Example test_add1: count 1 (add 1 [1;4;1]) = 3.
Proof. reflexivity. Qed.
Example test_add2: count 5 (add 1 [1;4;1]) = 0.
Proof. reflexivity. Qed.
Fixpoint member (v : nat) (s : bag) : bool :=
  match s with 
    | nil => false
    | h :: t => 
      match h =? v with
        | true => true
        | false => member v t
      end
  end.
Example test_member1: member 1 [1;4;1] = true.
Proof. reflexivity. Qed.
Example test_member2: member 2 [1;4;1] = false.
Proof. reflexivity. Qed.

(* Exercise end *)

(* Exercise: bag_more_functions *)
Fixpoint remove_one (v : nat) (s : bag) : bag :=
  match s with
    | h :: t => if h =? v then t else h :: remove_one v t
    | nil     => nil
  end.
Example test_remove_one1:
  count 5 (remove_one 5 [2;1;5;4;1]) = 0.
Proof. reflexivity. Qed.
Example test_remove_one2:
  count 5 (remove_one 5 [2;1;4;1]) = 0.
Proof. reflexivity. Qed.
Example test_remove_one3:
  count 4 (remove_one 5 [2;1;4;5;1;4]) = 2.
Proof. reflexivity. Qed.
Example test_remove_one4:
  count 5 (remove_one 5 [2;1;5;4;5;1;4]) = 1.
Proof. reflexivity. Qed.
Fixpoint remove_all (v:nat) (s:bag) : bag := 
match s with
  | h :: t => if h =? v then remove_all v t else h :: remove_all v t
  | nil     => nil
end.
Example test_remove_all1: count 5 (remove_all 5 [2;1;5;4;1]) = 0.
Proof. reflexivity. Qed.
Example test_remove_all2: count 5 (remove_all 5 [2;1;4;1]) = 0.
Proof. reflexivity. Qed.
Example test_remove_all3: count 4 (remove_all 5 [2;1;4;5;1;4]) = 2.
Proof. reflexivity. Qed.
Example test_remove_all4: count 5 (remove_all 5 [2;1;5;4;5;1;4;5;1;4]) = 0.
Proof. reflexivity. Qed.
Fixpoint included (s1 : bag) (s2 : bag) : bool :=
match s1 with
  | h :: t => if member h s2 then included t (remove_one h s2) else false
  | nil      => true
end.
Example test_included1: included [1;2] [2;1;4;1] = true.
Proof. reflexivity. Qed.
Example test_included2: included [1;2;2] [2;1;4;1] = false.
Proof. reflexivity. Qed.
(* Exercise end *)


(* Exercise: add_inc_count *)
Lemma add_nil: forall n, add n [] = [n].
Proof.
  reflexivity.
Qed.
Lemma count_n: forall n, count n [n] = 1.
Proof.
  intros n.
  induction n.
  - simpl. reflexivity.
  - simpl in IHn. simpl. assumption.
Qed.
Theorem add_inc_count : forall (v: nat) (l: bag), count v (add v l) = S (count v l).
Proof.
  intros.
  destruct l as [|h t].
  - rewrite -> add_nil. rewrite -> count_n. simpl. reflexivity.
  - simpl. rewrite -> eqb_refl. reflexivity.
Qed.
Definition manual_grade_for_add_inc_count : option (nat*string) := None.
(* Exercise end *)


(* Reasoning about lists *)

Theorem nil_app : forall l : natlist,
  [] ++ l = l.
Proof. reflexivity. Qed.
(* [] becomes the scrutinee of match *)

Theorem tl_length_pred : forall l:natlist,
  pred (length l) = length (tl l).
Proof.
  intros l. destruct l as [| n l'].
  - (* l = nil *)
    reflexivity.
  - (* l = cons n l' *)
    reflexivity. Qed.

(* Induction on Lists *)
Theorem app_assoc : forall l1 l2 l3 : natlist,
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  intros l1 l2 l3. induction l1 as [| n l1' IHl1'].
  - (* l1 = nil *)
    reflexivity.
  - (* l1 = cons n l1' *)
    simpl. rewrite -> IHl1'. reflexivity. Qed.

(* Generalizing Statements *)
Theorem repeat_double_firsttry : forall c n: nat,
  repeat n c ++ repeat n c = repeat n (c + c).
Proof.
  intros c. induction c as [| c' IHc'].
  - (* c = 0 *)
    intros n. simpl. reflexivity.
  - (* c = S c' *)
    intros n. simpl.
    (*  Now we seem to be stuck.  The IH cannot be used to 
        rewrite repeat n (c' + S c'): it only works
        for repeat n (c' + c'). If the IH were more liberal here
        (e.g., if it worked for an arbitrary second summand),
        the proof would go through. *)
Abort.

Theorem repeat_plus: forall c1 c2 n: nat,
    repeat n c1 ++ repeat n c2 = repeat n (c1 + c2).
Proof.
  intros c1 c2 n.
  induction c1 as [| c1' IHc1'].
  - simpl. reflexivity.
  - simpl.
    rewrite <- IHc1'.
    reflexivity.
  Qed.


(* Reversing a List *)

Fixpoint rev (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => rev t ++ [h]
  end.
Example test_rev1: rev [1;2;3] = [3;2;1].
Proof. reflexivity. Qed.
Example test_rev2: rev nil = nil.
Proof. reflexivity. Qed.

Theorem rev_length_firsttry : forall l : natlist,
  length (rev l) = length l.
Proof.
  intros l. induction l as [| n l' IHl'].
  - (* l = nil *)
    reflexivity.
  - (* l = n :: l' *)
    (* This is the tricky case.  Let's begin as usual
       by simplifying. *)
    simpl.
    (* Now we seem to be stuck: the goal is an equality
       involving ++, but we don't have any useful equations
       in either the immediate context or in the global
       environment!  We can make a little progress by using
       the IH to rewrite the goal... *)
    rewrite <- IHl'.
    (* ... but now we can't go any further. *)
Abort.

Theorem app_rev_length_S_firsttry: forall l n,
  length (rev l ++ [n]) = S (length (rev l)).
Proof.
  intros l. induction l as [| m l' IHl'].
  - (* l =  *)
    intros n. simpl. reflexivity.
  - (* l = m:: l' *)
    intros n. simpl.
    (* IHl' not applicable. *)
Abort.

Theorem app_length_S: forall l n,
  length (l ++ [n]) = S (length l).
Proof.
  intros l n. induction l as [| m l' IHl'].
  - (* l =  *)
    simpl. reflexivity.
  - (* l = m:: l' *)
    simpl.
    rewrite IHl'.
    reflexivity.
Qed.

Theorem app_length : forall l1 l2 : natlist,
  length (l1 ++ l2) = (length l1) + (length l2).
Proof.
  (* WORKED IN CLASS *)
  intros l1 l2. induction l1 as [| n l1' IHl1'].
  - (* l1 = nil *)
    reflexivity.
  - (* l1 = cons *)
    simpl. rewrite -> IHl1'. reflexivity. Qed.

Theorem rev_length : forall l : natlist,
  length (rev l) = length l.
Proof.
  intros l. induction l as [| n l' IHl'].
  - (* l = nil *)
    reflexivity.
  - (* l = cons *)
    simpl. rewrite -> app_length.
    simpl. rewrite -> IHl'. rewrite add_comm.
    reflexivity.
Qed.

(* Search *)
Search rev.
Search (_ + _ = _ + _).
Search (_ + _ = _ + _) inside Induction.
Search (?x + ?y = ?y + ?x). 
(* question mark indicates that it is a variable in the search pattern, 
rather than a defined identifier that is expected to be in scope currently *)


(* List Exercises *)

(* Exercise: list_exercises *)
Theorem app_nil_r : forall l : natlist,
  l ++ [] = l.
Proof.
  intros. 
  induction l.
  - reflexivity.
  - simpl. rewrite -> IHl. reflexivity.
Qed. 
Theorem rev_app_distr: forall l1 l2 : natlist,
  rev (l1 ++ l2) = rev l2 ++ rev l1. 
Proof.
  intros.
  induction l1.
  - simpl. rewrite -> app_nil_r. reflexivity.
  - simpl. rewrite -> IHl1. rewrite -> app_assoc. reflexivity.
Qed.

Theorem rev_involutive : forall l : natlist,
  rev (rev l) = l.
Proof.
  intros.
  induction l.
  - reflexivity.
  - simpl. rewrite -> rev_app_distr. rewrite -> IHl. reflexivity.
Qed.
Theorem app_assoc4 : forall l1 l2 l3 l4 : natlist,
  l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
Proof.
  intros.
  rewrite -> app_assoc.
  rewrite -> app_assoc.
  reflexivity.
Qed.

Lemma nonzeros_app : forall l1 l2 : natlist,
  nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
Proof.
  intros.
  induction l1.
  - simpl. reflexivity.
  - destruct n.
    + simpl. rewrite -> IHl1. reflexivity.
    + simpl. rewrite -> IHl1. reflexivity.
Qed.
(* Exercise end *)


(* Exercise: eqblist *)
Fixpoint eqblist (l1 l2 : natlist) : bool :=
  match l1, l2 with
    | n1 :: l1', n2 :: l2' => if n1 =? n2 then eqblist l1' l2' else false
    | nil, nil => true
    | _, _ => false
  end.
Example test_eqblist1 :
  (eqblist nil nil = true).
Proof. 
  reflexivity. Qed.
Example test_eqblist2 :
  eqblist [1;2;3] [1;2;3] = true.
Proof. 
  reflexivity. Qed.
Example test_eqblist3 :
  eqblist [1;2;3] [1;2;4] = false.
Proof. 
  reflexivity. Qed.

Theorem eqblist_refl : forall l:natlist,
  true = eqblist l l.
Proof.
  induction l as [| n l' IHl'].
  - reflexivity.
  - simpl. rewrite -> eqb_refl. rewrite <- IHl'. reflexivity.
Qed.
(* Exercise end *)

(* Exercise: count_member_nonzero *)
Theorem count_member_nonzero : forall (s : bag),
  1 <=? (count 1 (1 :: s)) = true.
Proof.
  simpl. reflexivity.
Qed.
(* Exercise end *)

Theorem leb_n_Sn : forall n,
  n <=? (S n) = true.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* 0 *)
    simpl. reflexivity.
  - (* S n' *)
    simpl. rewrite IHn'. reflexivity. Qed.

(* Exercise: remove_does_not_increase_count *)
Theorem remove_does_not_increase_count: forall (s : bag),
  (count 0 (remove_one 0 s)) <=? (count 0 s) = true.
Proof.
  induction s.
  - simpl. reflexivity.
  - destruct n.
    + simpl. rewrite -> leb_n_Sn. reflexivity.
    + simpl. rewrite -> IHs. reflexivity.
Qed.
(* Exercise end *)

(* Exercise: bag_count_sum *)
Theorem bag_count_sum: forall (s : bag),
  (count 0 (sum [] s)) =? (count 0 s) = true.
Proof.
  induction s as [|h t].
  - simpl. reflexivity.
  - destruct h.
    + simpl. rewrite -> eqb_refl. simpl. reflexivity.
    + simpl. rewrite -> eqb_refl. simpl. reflexivity.
Qed.
(* Exercise end *)

(* Exercise: involution_injective *)
Theorem involution_injective : 
  forall (f : nat -> nat),
  (forall n : nat, n = f (f n)) 
  -> (forall n1 n2 : nat, f n1 = f n2 -> n1 = n2).
Proof.
  intros f I n1 n2 H.
  rewrite -> I.
  rewrite <- H.
  rewrite <- I.
  reflexivity.
Qed.
(* Exercise end *)

(* Exercise: rev_injective *)
Theorem rev_injective : forall (l1 l2 : natlist),
  rev l1 = rev l2 -> l1 = l2.
Proof.
  intros.
  rewrite <- rev_involutive.
  rewrite <- H.
  rewrite -> rev_involutive.
  reflexivity.
Qed.
(* Exercise end *)

(* Options *)
Fixpoint nth_bad (l:natlist) (n:nat) : nat :=
  match l with
  | nil => 42
  | a :: l' => match n with
               | 0 => a
               | S n' => nth_bad l' n'
               end
  end.
(* Return error value *)
Inductive natoption : Type :=
  | Some (n : nat)
  | None.
Fixpoint nth_error (l:natlist) (n:nat) : natoption :=
  match l with
  | nil => None
  | a :: l' => match n with
               | O => Some a
               | S n' => nth_error l' n'
               end
  end.
Example test_nth_error1 : nth_error [4;5;6;7] 0 = Some 4.
Proof. reflexivity. Qed.
Example test_nth_error2 : nth_error [4;5;6;7] 3 = Some 7.
Proof. reflexivity. Qed.
Example test_nth_error3 : nth_error [4;5;6;7] 9 = None.
Proof. reflexivity. Qed.
Definition option_elim (d : nat) (o : natoption) : nat :=
  match o with
    | Some n' => n'
    | None => d
  end.

(* Exercise: hd_error *)
Definition hd_error (l : natlist) : natoption :=
  match l with
    | nil => None
    | h :: t => Some h
  end.
Example test_hd_error1 : hd_error [] = None.
Proof. reflexivity. Qed.
Example test_hd_error2 : hd_error [1] = Some 1.
Proof. reflexivity. Qed.
Example test_hd_error3 : hd_error [5;6] = Some 5.
Proof. reflexivity. Qed.
(* Exercise end *)

(* Exercise: option_elim_hd *)
Theorem option_elim_hd : forall (l:natlist) (default:nat),
  hd default l = option_elim default (hd_error l).
Proof.
  intros.
  destruct l.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed. 
(* Exercise end *)

End NatList.


(* Partial Maps *)
Inductive id : Type :=
  | Id (n : nat).
(* analogous to map or dictionary data structures *)
Definition eqb_id (x1 x2 : id) :=
  match x1, x2 with
  | Id n1, Id n2 => n1 =? n2
  end.

(* Exercise: eqb_id_refl *)
Theorem eqb_id_refl : forall x, eqb_id x x = true.
Proof.
  intros.
  destruct x.
  - simpl. rewrite -> eqb_refl. reflexivity. 
Qed.
(* Exercise end *)

Module PartialMap.
Export NatList. (* make the definitions from NatList available here *)
Inductive partial_map : Type :=
  | empty
  | record (i : id) (v : nat) (m : partial_map).

Definition update (d : partial_map)
                  (x : id) (value : nat)
                  : partial_map :=
  record x value d.

Fixpoint find (x : id) (d : partial_map) : natoption :=
  match d with
    | empty => None
    | record y v d' => if eqb_id x y
                      then Some v
                      else find x d'
  end.

(* Exercise: update_eq *)
Theorem update_eq :
  forall (d : partial_map) (x : id) (v: nat),
    find x (update d x v) = Some v.
Proof.
  simpl.
  intros.
  rewrite -> eqb_id_refl. 
  reflexivity.
Qed.
(* Exercise end *)


(* Exercise: update_neq *)
Theorem update_neq :
  forall (d : partial_map) (x y : id) (o: nat),
    eqb_id x y = false -> find x (update d y o) = find x d.
Proof.
  intros.
  simpl.
  rewrite -> H.
  reflexivity.
Qed.
(* Exercise end *)


End PartialMap.