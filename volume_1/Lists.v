From LF Require Export Induction.
From LF Require Export Basics.
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
  (* destruct (v =? v) eqn:Ev.
  - reflexivity.
  - simpl.  *)
  destruct l as [|h t].
  - rewrite -> add_nil. rewrite -> count_n. simpl. reflexivity.
  - simpl. 
    replace (v =? v) with true. 
    reflexivity.
    induction v as [| n' IHn'].
    + reflexivity.
    + simpl. rewrite <- IHn'. reflexivity.
Qed.
(* Exercise end *)


