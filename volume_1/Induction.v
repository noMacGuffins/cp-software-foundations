From LF Require Import Basics.

Print Basics.
(* Proof by Induction *)

(* try with reflexivity *)
Theorem add_0_r_firsttry : forall n:nat,
  n + 0 = n.
  Proof.
  intros n.
  simpl. (* Does nothing! *)
Abort.

(* try with destruct *)
Theorem add_0_r_secondtry : forall n:nat,
  n + 0 = n.
Proof.
  intros n. destruct n as [| n'] eqn:E.
  - (* n = 0 *)
    reflexivity. (* so far so good... *)
  - (* n = S n' *)
    simpl. (* ...but here we are stuck again *)
Abort.

(* 
Recall (from a discrete math course, probably) the principle of induction over natural numbers: If P(n) is some proposition involving a natural number n and we want to show that P holds for all numbers n, we can reason like this:
show that P(O) holds;
show that, for any n', if P(n') holds, then so does P(S n');
conclude that P(n) holds for all n.
 *)
(* Enter, induction! *)
Theorem add_0_r : forall n:nat, n + 0 = n.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *) reflexivity.
  - (* n = S n' *) simpl. rewrite -> IHn'. reflexivity. 
  Qed.

(* Exercise: basic_induction *)

Theorem mul_0_r : forall n:nat,
  n * 0 = 0.
Proof.
  induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite -> IHn'. reflexivity. Qed.
Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
  intros n m.
  induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite IHn'. reflexivity. Qed.
Theorem add_comm : forall n m : nat,
  n + m = m + n.
Proof.
  intros n m.
  induction n as [| n' IHn'].
  - simpl. rewrite <- plus_n_O. reflexivity.
  - simpl. rewrite -> IHn'. rewrite -> plus_n_Sm. reflexivity. Qed.
Theorem add_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p.
  induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite <- IHn'. reflexivity.
Qed.
(* Exercise end *)

(* Exercise: double_plus *)
Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Lemma double_plus : forall n, double n = n + n .
Proof.
  intros n.
  induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite -> IHn'.  rewrite <- plus_n_Sm. reflexivity.
  Qed.
(* Exercise end *)


(* Exercise: eqb_refl *)
Theorem eqb_refl : forall n : nat,
  (n =? n) = true.
Proof.
  intros n.
  induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite <- IHn'. reflexivity.
(* Exercise end *)

(* Exercise: even_S *)
Theorem even_S : forall n : nat,
  even (S n) = negb (even n).
Proof.
  intros n.
  induction n as [| n' IHn'].
  - reflexivity.
  - rewrite -> IHn'. rewrite -> negb_involutive.
(* Exercise end *)
  
(* Proofs within Proofs *)
(* trivial proof through assert *)
Theorem mult_0_plus' : forall n m : nat,
  (n + 0 + 0) * m = n * m.
Proof.
  intros n m.
  assert (H: n + 0 + 0 = n).
    { rewrite add_comm. simpl. rewrite add_comm. reflexivity. }
  rewrite -> H.
  reflexivity. Qed.
(* local lemmer for particular variables *)
Theorem plus_rearrange : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  assert (H: n + m = m + n).
  { rewrite add_comm. reflexivity. }
  rewrite H. reflexivity. Qed.

(* Formal vs Informal Proof *)
(* Associative property of addition formally *)
Theorem add_assoc'' : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p. induction n as [| n' IHn'].
  - (* n = 0 *)
    reflexivity.
  - (* n = S n' *)
    simpl. rewrite IHn'. reflexivity. Qed.
(* 
Corresponding informal proof 
Theorem: For any n, m and p,
      n + (m + p) = (n + m) + p.
Proof: By induction on n.
First, suppose n = 0. We must show that
        0 + (m + p) = (0 + m) + p.
This follows directly from the definition of +.
Next, suppose n = S n', where
        n' + (m + p) = (n' + m) + p.
We must now show that
        (S n') + (m + p) = ((S n') + m) + p.
By the definition of +, this follows from
        S (n' + (m + p)) = S ((n' + m) + p),
which is immediate from the induction hypothesis. Qed.
*)

(* Exercise: add_comm_informal *)
(* 
Theorem: Addition is commutative.
Proof: 
Suppose for any n and m,
      n + m = m + n
By induction on n.
First, suppose n = 0. We must show that
        0 + m = m + 0.
This follows directly from the definition of +.
Next, suppose n = S n', where
        n' + m = m + n'
We must now show that
        S n' + m = m + S n'.
By the definition of +, this follows from
        S (n' + m) = S (m + n'),
which is immediate from the induction hypothesis. Qed.
 *)
Definition manual_grade_for_add_comm_informal : option (nat*string) := None.
(* Exercise end *)

(* Exercise: eqb_refl_informal*)
Theorem eqb_refl : forall n : nat,
  (n =? n) = true.
Proof.
  intros n.
  induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite <- IHn'. reflexivity.
(* 
Theorem: (n =? n) = true for any n.
Proof: 
By induction on n.
First, suppose n = 0. We must show that
        (0 =? 0) = true
This follows directly which follows directy from the definition of =?.
Next, suppose n = S n', where
        S n' =? S n'
We must now show that
        S n' =? S n' = true.
Immediate from the induction hypothesis, 
        true = true.
 *)
(* Do not modify the following line: *)
Definition manual_grade_for_eqb_refl_informal : option (nat×string) := None.
(* Exercise end *)

