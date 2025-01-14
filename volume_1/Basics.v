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

Module TuplePlayground.
  Inductive bit : Type :=
    | B1
    | B0.
  Inductive nybble : Type :=
    | bits (b0 b1 b2 b3 : bit).
  Check (bits B1 B0 B1 B0)
    : nybble.
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

(* proof by simplication *)
(* ∀ in the html => forall in coq
actually dont need simpl, reflexivity does the work *)
Theorem plus_O_n' : forall n : nat, 0 + n = n.
Proof.
  intros n. reflexivity. Qed.
(* variable does not have to match when moving from quantifier to the context *)
Theorem plus_O_n'' : forall n : nat, 0 + n = n.
Proof.
  intros m. reflexivity. Qed.

(* similarly *)
Theorem plus_1_l : forall n:nat, 1 + n = S n.
Proof.
  intros n. reflexivity. Qed.
Theorem mult_0_l : forall n:nat, 0 * n = 0.
Proof.
  intros n. reflexivity. Qed.

(* proof by rewriting *)
Theorem plus_id_example : forall n m:nat,
  n = m ->
  n + n = m + m.
Proof.
  (* move both quantifiers into the context: *)
  intros n m.
  (* move the hypothesis into the context: *)
  intros H.
  (* rewrite the goal using the hypothesis: *)
  rewrite -> H.
  reflexivity. Qed.

(* Exercise: plus_id *)
Theorem plus_id_exercise : forall n m o : nat,
  n = m -> 
  m = o -> 
  n + m = m + o.
Proof.
  intros n m o.
  intros H1.
  intros H2.
  rewrite -> H1.
  rewrite -> H2. 
  reflexivity. Qed.
(* Exercise end *)

(* using previously proven theorems *)
Theorem mult_n_0_m_0 : forall p q : nat,
  (p *0) + (q * 0) = 0.
Proof.
  intros p q.
  rewrite <- mult_n_O.
  rewrite <- mult_n_O.
  reflexivity. Qed.

Check mult_n_O.
(* Exercise  *)
Theorem mult_n_1 : forall p : nat,
  p * 1 = p.
Proof.
  intros p.
  rewrite <- mult_n_Sm.
  rewrite <- mult_n_O.
  reflexivity. Qed.

(* proof by case analysis: basically match within a proof *)
Theorem plus_1_neq_0 : forall n : nat,
  (n + 1) =? 0 = false.
Proof.
  intros n. destruct n as [| n'] eqn:E.
  - reflexivity.
  - reflexivity. Qed.

Theorem negb_involutive : forall b : bool,
  negb (negb b) = b.
Proof.
  intros b. destruct b eqn:E.
  - reflexivity.
  - reflexivity. Qed.

Theorem andb_commutative : forall b c, andb b c = andb c b.
Proof.
  intros b c. destruct b eqn:Eb.
  - destruct c eqn:Ec.
    + reflexivity.
    + reflexivity.
  - destruct c eqn:Ec.
    + reflexivity.
    + reflexivity.
Qed.
Theorem andb_commutative' : forall b c, andb b c = andb c b.
Proof.
  intros b c. destruct b eqn:Eb.
  { destruct c eqn:Ec.
    { reflexivity. }
    { reflexivity. } }
  { destruct c eqn:Ec.
    { reflexivity. }
    { reflexivity. } }
Qed.

(* curly braces also possible to separate subgoals *)
Theorem andb3_exchange :
  forall b c d, andb (andb b c) d = andb (andb b d) c.
Proof.
  intros b c d. destruct b eqn:Eb.
  - destruct c eqn:Ec.
    { destruct d eqn:Ed.
      - reflexivity.
      - reflexivity. }
    { destruct d eqn:Ed.
      - reflexivity.
      - reflexivity. }
  - destruct c eqn:Ec.
    { destruct d eqn:Ed.
      - reflexivity.
      - reflexivity. }
    { destruct d eqn:Ed.
      - reflexivity.
      - reflexivity. }
Qed.

(* Exercise: andb_true_elim2 *)
Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
Proof.
  intros b c.
  destruct b eqn: Eb.
  {
    simpl.
    intros H.
    rewrite -> H.
    reflexivity.
  }
  {
    simpl.
    intros H.
    destruct c.
    - reflexivity.
    - rewrite <- H.
    reflexivity.
  }
Qed.
(* Exercise end *)

(* Exercise: zero_nbeq_plus_1 *)
Theorem zero_nbeq_plus_1 : forall n : nat,
  0 =? (n + 1) = false.
Proof.
  intros n.
  destruct n.
  {
    simpl.
    reflexivity.
  }
  {
    simpl.
    reflexivity.
  }
  Qed.
(* Exercise end *)

(* shorthand *)
Theorem plus_1_neq_0' : forall n : nat,
  (n + 1) =? 0 = false.
Proof.
  intros [|n].
  - reflexivity.
  - reflexivity. Qed.

Theorem andb_commutative'' :
  forall b c, andb b c = andb c b.
Proof.
  intros [] [].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

(* Exercise: identity_fn_applied_twice *)
Theorem identity_fn_applied_twice :
  forall (f : bool -> bool),
  (forall (x : bool), f x = x) ->
  forall (b : bool), f (f b) = b.
Proof.
  intros f x b.
  rewrite-> x.
  rewrite-> x.
  reflexivity.
Qed.

(* Exercise: negation_fn_applied_twice *)
Theorem negation_fn_applied_twice:
  forall (f : bool -> bool),
  (forall (x : bool), f x = negb x) ->
  forall (b : bool), f (f b) = b.
Proof.
  intros f x b.
  rewrite-> x.
  rewrite-> x.
  destruct b.
  - reflexivity.
  - reflexivity.
Qed.
(* Exercise end *)

Definition manual_grade_for_negation_fn_applied_twice : option (nat*string) := None.

(* Exercise: andb_eq_orb *)
Theorem andb_eq_orb :
  forall (b c : bool),
  (andb b c = orb b c) ->
  b = c.
Proof.
  intros b c. destruct b eqn:Eb.
  {
    destruct c eqn:Ec.
    - reflexivity.
    - simpl.
      intro H.
      rewrite -> H.
      reflexivity.
  }
  {
    destruct c eqn:Ec.
    - simpl.
      intro H.
      rewrite -> H.
      reflexivity.
    - reflexivity.
  }
Qed.
(* Exercise end *)

Module LateDays.
  Inductive letter : Type :=
  | A | B | C | D | F.
  Inductive modifier : Type :=
  | Plus | Natural | Minus.
  Inductive grade : Type :=
  Grade (l:letter) (m:modifier).
  Inductive comparison : Type :=
  | Eq (* "equal" *)
  | Lt (* "less than" *)
  | Gt. (* "greater than" *)
  Definition letter_comparison (l1 l2 : letter) : comparison :=
    match l1, l2 with
    | A, A => Eq
    | A, _ => Gt
    | B, A => Lt
    | B, B => Eq
    | B, _ => Gt
    | C, (A | B) => Lt
    | C, C => Eq
    | C, _ => Gt
    | D, (A | B | C) => Lt
    | D, D => Eq
    | D, _ => Gt
    | F, (A | B | C | D) => Lt
    | F, F => Eq
    end.

(* Exercise: letter_comparison *)
Theorem letter_comparison_Eq :
  forall l, letter_comparison l l = Eq.
Proof.
  intros [].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.
(* Exercise end *)

Definition modifier_comparison (m1 m2 : modifier) : comparison :=
  match m1, m2 with
  | Plus, Plus => Eq
  | Plus, _ => Gt
  | Natural, Plus => Lt
  | Natural, Natural => Eq
  | Natural, _ => Gt
  | Minus, (Plus | Natural) => Lt
  | Minus, Minus => Eq
  end.

(* Exercise: letter_comparison *)
Definition grade_comparison (g1 g2 : grade) : comparison :=
  match g1, g2 with
  | (Grade letter1 modifier1), (Grade letter2 modifier2) => 
    match (letter_comparison letter1 letter2) with
      | Eq => modifier_comparison modifier1 modifier2
      | _ => letter_comparison letter1 letter2
    end
  end.

Example test_grade_comparison1 :
  (grade_comparison (Grade A Minus) (Grade B Plus)) = Gt.
reflexivity. Qed.
Example test_grade_comparison2 :
  (grade_comparison (Grade A Minus) (Grade A Plus)) = Lt.
reflexivity. Qed.
Example test_grade_comparison3 :
  (grade_comparison (Grade F Plus) (Grade F Plus)) = Eq.
reflexivity. Qed.
Example test_grade_comparison4 :
  (grade_comparison (Grade B Minus) (Grade C Plus)) = Gt.
reflexivity. Qed.
(* Exercise end *)


Definition lower_letter (l : letter) : letter :=
  match l with
  | A => B
  | B => C
  | C => D
  | D => F
  | F => F (* Can't go lower than F! *)
  end.

Theorem lower_letter_lowers: forall (l : letter),
  letter_comparison (lower_letter l) l = Lt.
Proof.
  intros l.
  destruct l.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. (* We get stuck here. *)
Abort.

(* reason *)
Theorem lower_letter_F_is_F:
  lower_letter F = F.
Proof.
  simpl. reflexivity.
Qed.

(* Exercise: lower_letter_lowers *)
Theorem lower_letter_lowers:
  forall (l : letter),
    letter_comparison F l = Lt ->
    letter_comparison (lower_letter l) l = Lt.
Proof.
  intros [].
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - simpl.
      intros H.
      rewrite H.
      reflexivity.
  Qed.
(* Exercise end *)

(* Exercise: lower_grade *)
Definition lower_grade (g : grade) : grade :=
  match g with
  | (Grade letter modifier) => 
    match modifier with
      | Plus => Grade letter Natural
      | Natural => Grade letter Minus
      | Minus => 
        match letter with
        | F => g
        | _ => Grade (lower_letter letter) Plus
        end
    end
  end.

Example lower_grade_A_Plus :
  lower_grade (Grade A Plus) = (Grade A Natural).
Proof.
reflexivity. Qed.
Example lower_grade_A_Natural :
  lower_grade (Grade A Natural) = (Grade A Minus).
Proof.
reflexivity. Qed.
Example lower_grade_A_Minus :
  lower_grade (Grade A Minus) = (Grade B Plus).
Proof.
reflexivity. Qed.
Example lower_grade_B_Plus :
  lower_grade (Grade B Plus) = (Grade B Natural).
Proof.
reflexivity. Qed.
Example lower_grade_F_Natural :
  lower_grade (Grade F Natural) = (Grade F Minus).
Proof.
reflexivity. Qed.
Example lower_grade_twice :
  lower_grade (lower_grade (Grade B Minus)) = (Grade C Natural).
Proof.
reflexivity. Qed.
Example lower_grade_thrice :
  lower_grade (lower_grade (lower_grade (Grade B Minus))) = (Grade C Minus).
Proof.
reflexivity. Qed.
Theorem lower_grade_F_Minus : lower_grade (Grade F Minus) = (Grade F Minus).
Proof.
reflexivity. Qed.
(* Exercise end *)

(* Exercise: lower_grade_lowers *)
Theorem lower_grade_lowers :
  forall (g : grade),
    grade_comparison (Grade F Minus) g = Lt ->
    grade_comparison (lower_grade g) g = Lt.
Proof.
  intros [] H. 
  simpl.
  destruct m.
  {
    simpl.
    rewrite -> letter_comparison_Eq.
    reflexivity.
  }
  {
    simpl.
    rewrite -> letter_comparison_Eq.
    reflexivity.
  }
  {
    simpl.
    destruct l.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - rewrite -> H.
      reflexivity.
  }
Qed.
  (* Exercise end *)

Definition apply_late_policy (late_days : nat) (g : grade) : grade :=
  if late_days <? 9 then g
  else if late_days <? 17 then lower_grade g
  else if late_days <? 21 then lower_grade (lower_grade g)
  else lower_grade (lower_grade (lower_grade g)).

Theorem apply_late_policy_unfold :
  forall (late_days : nat) (g : grade),
    (apply_late_policy late_days g)
    =
    (if late_days <? 9 then g else
       if late_days <? 17 then lower_grade g
       else if late_days <? 21 then lower_grade (lower_grade g)
            else lower_grade (lower_grade (lower_grade g))).
Proof.
  intros. reflexivity.
Qed.

(* Exercise: no_penalty_for_mostly_on_time *)
  Theorem no_penalty_for_mostly_on_time :
    forall (late_days : nat) (g : grade),
      (late_days <? 9 = true) ->
      apply_late_policy late_days g = g.
  Proof.
    intros.
    rewrite -> apply_late_policy_unfold.
    rewrite H.
    reflexivity.
Qed.
(* Exercise end *)


(* Exercise: grade_lowered_once *)
Theorem grade_lowered_once :
  forall (late_days : nat) (g : grade),
    (late_days <? 9 = false) ->
    (late_days <? 17 = true) ->
    (apply_late_policy late_days g) = (lower_grade g).
Proof.
  intros.
    rewrite -> apply_late_policy_unfold.
    rewrite H.
    rewrite H0.
    reflexivity.
Qed.
(* Exercise end *)
End LateDays.

(* Exercise: binary numerals *)

Inductive bin : Type :=
  | Z
  | B0 (n : bin)
  | B1 (n : bin).

Fixpoint incr (m:bin) : bin :=
  match m with
    | Z => B1 (Z)
    | B0 (n) => B1 (n)
    | B1 (n) => B0 (incr (n))
  end.
  
Fixpoint bin_to_nat (m:bin) : nat :=
  match m with
    | B0 (n) => 2 * bin_to_nat(n)
    | B1 (n) => 1 + 2 * bin_to_nat(n)
    | Z => 0
  end.

Example test_bin_incr1 : (incr (B1 Z)) = B0 (B1 Z).
reflexivity. Qed.
Example test_bin_incr2 : (incr (B0 (B1 Z))) = B1 (B1 Z).
reflexivity. Qed.
Example test_bin_incr3 : (incr (B1 (B1 Z))) = B0 (B0 (B1 Z)).
simpl. reflexivity. Qed.
Example test_bin_incr4 : bin_to_nat (B0 (B1 Z)) = 2.
reflexivity. Qed.
Example test_bin_incr5 :
        bin_to_nat (incr (B1 Z)) = 1 + bin_to_nat (B1 Z).
reflexivity. Qed.
Example test_bin_incr6 :
        bin_to_nat (incr (incr (B1 Z))) = 2 + bin_to_nat (B1 Z).
reflexivity. Qed.

(* Exercise end *)