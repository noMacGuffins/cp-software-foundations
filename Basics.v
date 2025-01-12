Inductive day : Type :=
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday.

Definition next_working_day (d:day) : day :=
  match d with
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => monday
  | saturday => monday
  | sunday => monday
  end.

Compute (next_working_day friday).
(* simplify as much as possible *)

Example test_next_working_day:
  (next_working_day (next_working_day saturday)) = tuesday.
(* Example/Theorem/Lemma/Proposition takes you to proof mode *)

Proof. simpl. reflexivity. Qed.
(* 
- simpl reduces a goal as much as possible 
- reflexivity is particular to equality proofs if generates no subgoal if the left and right hand side is indeed the same
- Qed takes you back from proving mode back to the top level
 *)

Print test_next_working_day.
(* prove in just two steps: eq_refl? is the proof object + defines equality in coq *)

From Coq Require Export String.

Inductive bool : Type :=
  | true
  | false.

Definition negb (b:bool) : bool :=
  match b with
  | true => false
  | false => true
  end.
Definition andb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.
Definition orb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => true
  | false => b2
  end.

(* just to see how its done *)

Example test_orb1: (orb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb2: (orb false false) = false.
Proof. simpl. reflexivity. Qed.
Example test_orb3: (orb false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb4: (orb true true) = true.
Proof. simpl. reflexivity. Qed.

(* concrete syntax for multiargument functions: listed are basically unit tests *)

Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).
Example test_orb5: false || false || true = true.
Proof. simpl. reflexivity. Qed.

(* defining new notation *)

Definition negb' (b:bool) : bool :=
  if b then false
  else true.
Definition andb' (b1:bool) (b2:bool) : bool :=
  if b1 then b2
  else false.
Definition orb' (b1:bool) (b2:bool) : bool :=
  if b1 then true
  else b2.

(* conditional expression but with one generalization: 
The guard is considered true if it evaluates to the "constructor" of the first clause of the Inductive definition *)

(* Exercise: nandb *)
Definition nandb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | false => true
  | true => negb b2
  end.

Example test_nandb1: (nandb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb2: (nandb false false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb3: (nandb false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb4: (nandb true true) = false.
Proof. simpl. reflexivity. Qed.
(* Exercise end *)

(* Exercise: andb3 *)
Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool :=
  match b1 with
  | false => b1
  | true => andb b2 b3
  end.
Example test_andb31: (andb3 true true true) = true.
Proof. simpl. reflexivity. Qed.
Example test_andb32: (andb3 false true true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb33: (andb3 true false true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb34: (andb3 true true false) = false.
Proof. simpl. reflexivity. Qed.
(* Exercise end *)

Check true.
(* returns type *)

Check true
  : bool.
Check (negb true)
  : bool.
(* can also verify type *)

Check negb
  : bool -> bool.
(* functions are also values with their own type depending on their inputs and output*)


(* new types from old *)
Inductive rgb : Type :=
  | red
  | green
  | blue.
Inductive color : Type :=
  | black
  | white
  | primary (p : rgb).

Definition monochrome (c : color) : bool :=
  match c with
  | black => true
  | white => true
  | primary p => false
  end.

Definition isred (c : color) : bool :=
  match c with
  | black => false
  | white => false
  | primary red => true
  | primary _ => false
  end.

(* modules *)
Module Playground.
  Definition foo : rgb := blue.
End Playground.

Definition foo : bool := true.
Check Playground.foo : rgb.
Check foo : bool.

(* tuples *)
Inductive bit : Type :=
  | B1
  | B0.
Inductive nybble : Type :=
  | bits (b0 b1 b2 b3 : bit).
Check (bits B1 B0 B1 B0)
  : nybble.

Module TuplePlayground.
    Definition all_zero (nb : nybble) : bool :=
    match nb with
    | (bits B0 B0 B0 B0) => true
    | (bits _ _ _ _) => false
    end.
    Compute (all_zero (bits B1 B0 B1 B0)).
    (* ===> false : bool *)
    Compute (all_zero (bits B0 B0 B0 B0)).
    (* ===> true : bool *)
End TuplePlayground.

(* natural numbers: unary representation *)
Module NatPlayground.
Inductive nat : Type :=
  | O
  | S (n : nat).
Inductive otherNat : Type :=
  | stop
  | tick (foo : otherNat).
Definition pred (n : nat) : nat :=
  match n with
  | O => O
  | S n' => n'
  end.
End NatPlayground.

Check (S (S (S (S O)))).
Definition minustwo (n : nat) : nat :=
  match n with
  | O => O
  | S O => O
  | S (S n') => n'
  end.
Compute (minustwo 4).

(* recursion: use fixpoint instead of definiton *)
Fixpoint even (n:nat) : bool :=
match n with
| O => true
| S O => false
| S (S n') => even n'
end.

Definition odd (n:nat) : bool :=
negb (even n).
Example test_odd1: odd 1 = true.
Proof. simpl. reflexivity. Qed.
Example test_odd2: odd 4 = false.
Proof. simpl. reflexivity. Qed.


Module NatPlayground2.
Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
  | O => m
  | S n' => S (plus n' m)
  end.
  Compute (plus 3 2).

  (* notational convenience *)
Fixpoint mult (n m : nat) : nat :=
  match n with
  | O => O
  | S n' => plus m (mult n' m)
  end.
Example test_mult1: (mult 3 3) = 9.
Proof. simpl. reflexivity. Qed.

(* match two expressions at once *)
Fixpoint minus (n m:nat) : nat :=
  match n, m with
  | O , _ => O
  | S _ , O => n
  | S n', S m' => minus n' m'
  end.
End NatPlayground2.
Fixpoint exp (base power : nat) : nat :=
  match power with
  | O => S O
  | S p => mult base (exp base p)
  end.

(* Exercise: factorial *)
Fixpoint factorial (n:nat) : nat :=
  match n with
  | 0 => 1
  | S n' => mult n (factorial n')
  end.
Example test_factorial1: (factorial 3) = 6.
Proof. simpl. reflexivity. Qed.
Example test_factorial2: (factorial 5) = (mult 10 12).
Proof. simpl. reflexivity. Qed.
(* Exercise end *)


(* notation cont.. *)
Notation "x + y" := (plus x y)
                       (at level 50, left associativity)
                       : nat_scope.
Notation "x - y" := (minus x y)
                       (at level 50, left associativity)
                       : nat_scope.
Notation "x * y" := (mult x y)
                       (at level 40, left associativity)
                       : nat_scope.
Check ((0 + 1) + 1) : nat.

(* equality for nat *)
Fixpoint eqb (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => eqb n' m'
            end
  end.
Fixpoint leb (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => leb n' m'
      end
  end.
Example test_leb1: leb 2 2 = true.
Proof. simpl. reflexivity. Qed.
Example test_leb2: leb 2 4 = true.
Proof. simpl. reflexivity. Qed.
Example test_leb3: leb 4 2 = false.
Proof. simpl. reflexivity. Qed.

(* corresponding infix notations *)
Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.
Notation "x <=? y" := (leb x y) (at level 70) : nat_scope.
Example test_leb3': (4 <=? 2) = false.
Proof. simpl. reflexivity. Qed.


(* Exercise ltb *)
Definition ltb (n m : nat) : bool :=
  match m with
  | 0 => false
  | S m' => leb  n m'
  end.
Notation "x <? y" := (ltb x y) (at level 70) : nat_scope.
Example test_ltb1: (ltb 2 2) = false.
Proof. simpl. reflexivity. Qed.
Example test_ltb2: (ltb 2 4) = true.
Proof. simpl. reflexivity. Qed.
Example test_ltb3: (ltb 4 2) = false.
Proof. simpl. reflexivity. Qed.
(* Exercise end *)


