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
  - simpl. rewrite -> add_0_r. reflexivity.
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
  - rewrite -> IHn'. rewrite -> negb_involutive. reflexivity.
Qed.
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
Qed.
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
Definition manual_grade_for_eqb_refl_informal : option (nat*string) := None.
(* Exercise end *)

(* Exercise: mul_comm *)
Theorem add_shuffle3 : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  rewrite -> add_assoc.
  rewrite -> add_assoc.
  assert (H: n + m = m + n).
  { rewrite add_comm. reflexivity. }
  rewrite -> H.
  reflexivity.
Qed.

Theorem mul_comm : forall m n : nat,
  m * n = n * m.
Proof.
  intros m n.
  induction m.
  {
    induction n.
    - reflexivity.
    - simpl. rewrite <- IHn. reflexivity.
  }
  {
    induction n.
    - simpl. rewrite -> IHm. reflexivity.
    - simpl. 
      rewrite -> IHm. 
      simpl.
      rewrite <- mult_n_Sm.
      rewrite -> add_comm.
      rewrite -> add_assoc.
      reflexivity.
  }
Qed.
(* Exercise end *)

(* Exercise: plus_leb_compat_l *)
Theorem plus_leb_compat_l : forall n m p : nat,
  n <=? m = true -> (p + n) <=? (p + m) = true.
Proof.
  intros n m p IHn.
  induction p.
  - simpl. rewrite -> IHn. reflexivity.
  - simpl. rewrite -> IHp. reflexivity.
Qed.
(* Exercise end *)

(* Exercise: more exercises *)
Theorem leb_refl : forall n:nat,
  (n <=? n) = true.
Proof.
  intros n.
  induction n.
  - reflexivity.
  - simpl. rewrite -> IHn. reflexivity.
  Qed.
Theorem zero_neqb_S : forall n:nat,
  0 =? (S n) = false.
Proof.
  intros. 
  destruct n.
  - reflexivity.
  - reflexivity. 
  Qed.
Theorem andb_false_r : forall b : bool,
  andb b false = false.
Proof.
  intros b.
  destruct b.
  - reflexivity.
  - reflexivity.
  Qed.
Theorem S_neqb_0 : forall n:nat,
  (S n) =? 0 = false.
Proof.
  simpl. reflexivity. Qed.
Theorem mult_1_l : forall n:nat, 1 * n = n.
Proof.
  intros n. simpl. rewrite -> add_0_r. reflexivity. Qed.
Theorem all3_spec : forall b c : bool,
  orb
    (andb b c)
    (orb (negb b)
         (negb c))
  = true.
Proof.
  intros b c.
  destruct b, c.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.
Theorem mult_plus_distr_r : forall n m p : nat,
  (n + m) * p = (n * p) + (m * p).
Proof.
  intros n m p. 
  induction p.
  {
    rewrite -> mul_0_r. 
    rewrite -> mul_0_r. 
    rewrite -> mul_0_r.
    reflexivity.
  }
  {
    rewrite <- mult_n_Sm.
    rewrite <- mult_n_Sm.
    rewrite <- mult_n_Sm.
    rewrite -> IHp.
    assert (H1: n * p + m * p + (n + m) = n * p + (m * p + (n + m))).
    { rewrite <- add_assoc. reflexivity. }
    rewrite -> H1.
    assert (H2: n * p + n + (m * p + m) = n * p + (n + (m * p + m))).
    { rewrite <- add_assoc. reflexivity. }
    rewrite -> H2.
    assert (H3: n + (m * p + m) = n + m * p + m).
    { rewrite <- add_assoc. reflexivity. }
    rewrite -> H3.
    assert (H4: n + m * p = m * p + n).
    { rewrite -> add_comm. reflexivity. }
    rewrite -> H4.
    rewrite -> add_assoc.
    rewrite -> add_assoc.
    rewrite -> add_assoc.
    rewrite -> add_assoc.
    reflexivity.
  }
Qed.
Theorem mult_assoc : forall n m p : nat,
  n * (m * p) = (n * m) * p.
Proof.
  intros n m p.
  induction n.
  - reflexivity.
  - simpl. rewrite -> IHn. rewrite <- mult_plus_distr_r. reflexivity.
  Qed.

(* Exercise end *)

(* Exercise: add_shuffle3' *)
Theorem add_shuffle3' : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  rewrite -> add_assoc.
  rewrite -> add_assoc.
  replace (n + m) with (m + n). reflexivity.
  rewrite -> add_comm.
  reflexivity.
  Qed.
(* Exercise end *)

(* Nat back to Bin and Back to Nat *)
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

(* Exercise: binary_commute *)
Theorem bin_to_nat_pres_incr : forall b : bin,
  bin_to_nat (incr b) = 1 + bin_to_nat b.
Proof.
  simpl.
  intros b.
  induction b.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. rewrite -> IHb. simpl. rewrite <- plus_n_Sm. reflexivity.
Qed.
(* Exercise end *)

(* Exercise: nat_to_bin *)
Fixpoint nat_to_bin (n:nat) : bin :=
  match n with
    | 0 => Z
    | S(n') => incr(nat_to_bin(n'))
  end.
  
Theorem nat_bin_nat : forall n, bin_to_nat (nat_to_bin n) = n.
Proof.
  intros n.
  induction n.
  - reflexivity.
  - simpl.
    rewrite -> bin_to_nat_pres_incr.
    rewrite -> IHn.
    reflexivity.
Qed.
(* Exercise end *)

(* Bin to Nat and back *)
Theorem bin_nat_bin_fails : forall b, nat_to_bin (bin_to_nat b) = b.
Abort.

(* Exercise: double_bin *)
Lemma double_incr : forall n : nat, double (S n) = S (S (double n)).
Proof.
  destruct n.
  - reflexivity.
  - reflexivity.
Qed.

Definition double_bin (b:bin) : bin := 
  match b with
    | Z => Z
    | n => B0 n
  end.

Example double_bin_zero : double_bin Z = Z.
Proof. reflexivity.  Qed.

Lemma double_incr_bin : forall b,
    double_bin (incr b) = incr (incr (double_bin b)).
Proof.
  induction b.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.
(* Exercise end *)

(* Exercise: bin_nat_bin *)

(* Exercise end *)

