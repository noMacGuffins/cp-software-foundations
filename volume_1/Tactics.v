From LF Require Export Poly.

(* The apply tactic *)
Theorem silly1 : forall (n m : nat),
  n = m ->
  n = m.
Proof.
  intros n m eq.
  apply eq. Qed.

Theorem silly2 : forall (n m o p : nat),
  n = m ->
  (n = m -> [n;o] = [m;p]) ->
  [n;o] = [m;p].
Proof.
  intros n m o p eq1 eq2.
  apply eq2. apply eq1. Qed.

Theorem silly2a : forall (n m : nat),
  (n,n) = (m,m) ->
  (forall (q r : nat), (q,q) = (r,r) -> [q] = [r]) ->
  [n] = [m].
Proof.
  intros n m eq1 eq2.
  apply eq2. apply eq1. Qed.


(* Exercise: 2 stars, standard, optional (silly_ex) *)
Theorem silly_ex : forall p,
  (forall n, even n = true -> even (S n) = false) ->
  (forall n, even n = false -> odd n = true) ->
  even p = true ->
  odd (S p) = true.
Proof.
    intros p eq1 eq2 eq3.
    apply eq2. apply eq1. apply eq3. Qed.

Theorem silly3 : forall (n m : nat),
  n = m ->
  m = n.
Proof.
  intros n m H.
  Fail apply H.
  symmetry. apply H. Qed.

(* Exercise end *)

(* Exercise: 3 stars, standard, recommended (apply_exercise1) *)
Search rev.
Theorem rev_exercise1 : forall (l l' : list nat),
  l = rev l' ->
  l' = rev l.
Proof.
  intros l l' eq.
  rewrite -> eq.
  symmetry.
  apply rev_involutive. Qed.
(* Exercise end *)

(* Exercise: 1 star, standard, optional (apply_rewrite) *)
(* 
rewrite simply replaces expressions 
while apply solves goals directly after replacing expressions *)

(* Exercise end *)

(* Exercise: The apply with Tactic *)

Example trans_eq_example : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  rewrite -> eq1. rewrite -> eq2. reflexivity. Qed.

Theorem trans_eq : forall (X:Type) (n m o : X),
  n = m -> m = o -> n = o.
Proof.
  intros X n m o eq1 eq2. rewrite -> eq1. rewrite -> eq2.
  reflexivity. Qed.

Example trans_eq_example' : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
   apply trans_eq with (m:=[c;d]). (* with no required *)
  apply eq1. apply eq2. Qed.

Example trans_eq_example'' : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  transitivity [c;d]. (* built in transitivity also does the work *)
  apply eq1. apply eq2. Qed.
  
(* Exercise: trans_eq_exercise *)
Example trans_eq_exercise : forall (n m o p : nat),
     m = (minustwo o) ->
     (n + p) = m ->
     (n + p) = (minustwo o).
Proof.
  intros.
  transitivity m.
  - apply H0.
  - apply H. Qed.
(* Exercise end  *)

(* Exercise: The injection and discriminate Tactics *)
(* 
 Inductive nat : Type :=
       | O // injective
       | S (n : nat). // disjoint
 *)

(*  injection that allows us to exploit the injectivity of any constructor *)
Theorem S_injective : forall (n m : nat),
  S n = S m ->
  n = m.
Proof.
  intros n m H1.
  assert (H2: n = pred (S n)). { reflexivity. }
  rewrite H2. rewrite H1. simpl. reflexivity.
Qed.

Theorem S_injective' : forall (n m : nat),
  S n = S m ->
  n = m.
Proof.
  intros n m H.
  injection H as Hnm. apply Hnm.
Qed.

Theorem injection_ex1 : forall (n m o : nat),
  [n;m] = [o;o] ->
  n = m.
Proof.
  intros n m o H.
  (* WORKED IN CLASS *)
  injection H as H1 H2.
  rewrite H1. rewrite H2. reflexivity.
Qed.


(* Exercise: injection_ex3 *)

Example injection_ex3 : forall (X : Type) (x y z : X) (l j : list X),
  x :: y :: l = z :: j ->
  j = z :: l ->
  x = y.
Proof.
  intros.
  rewrite H0 in H.
  injection H as H1 H2.
  rewrite H1. rewrite H2. reflexivity. Qed.
(* Exercise end *)


Theorem discriminate_ex1 : forall (n m : nat),
  false = true ->
  n = m.
Proof.
  intros n m contra. discriminate contra. Qed.
Theorem discriminate_ex2 : forall (n : nat),
  S n = O ->
  2 + 2 = 5.
Proof.
  intros n contra. discriminate contra. Qed.


(* Exercise: discriminate_ex3 *)

Example discriminate_ex3 : forall (X : Type) (x y z : X) (l j : list X),
  x :: y :: l = [] ->
  x = z.
Proof.
  intros.
  discriminate H. Qed.
(* Exercise end *)

Theorem eqb_0_l : forall n,
   0 =? n = true -> n = 0.
Proof.
  intros n.
  destruct n as [| n'] eqn:E.
  - (* n = 0 *)
    intros H. reflexivity.
  - (* n = S n' *)
    simpl.
    intros H. discriminate H. Qed.

Theorem f_equal : forall (A B : Type) (f: A -> B) (x y: A),
  x = y -> f x = f y.
Proof. intros A B f x y eq. rewrite eq. reflexivity. Qed.
Theorem eq_implies_succ_equal : forall (n m : nat),
  n = m -> S n = S m.
Proof. intros n m H. apply f_equal. apply H. Qed.

Theorem eq_implies_succ_equal' : forall (n m : nat),
  n = m -> S n = S m.
Proof. intros n m H. f_equal. apply H. Qed. (* built in function *)


(* Using Tactics on Hypotheses *)

Theorem S_inj : forall (n m : nat) (b : bool),
  ((S n) =? (S m)) = b ->
  (n =? m) = b.
Proof.
  intros n m b H. simpl in H. apply H. Qed.

Theorem silly4 : forall (n m p q : nat),
  (n = m -> p = q) ->
  m = n ->
  q = p.
Proof.
  intros n m p q EQ H.
  symmetry in H. apply EQ in H. symmetry in H.
  apply H. Qed.


(* Specializing Hypotheses *)

Theorem specialize_example: forall n,
     (forall m, m*n = 0)
  -> n = 0.
Proof.
  intros n H.
  specialize H with (m := 1).
  simpl in H.
  rewrite add_comm in H.
  simpl in H.
  apply H. Qed.

Example trans_eq_example''' : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  Check trans_eq.
  specialize trans_eq with (m:=[c;d]) as H.
  apply H.
  apply eq1.
  apply eq2. Qed.

(* Varying the Induction Hypothesis *)

(* using intros carefully *)
Theorem double_injective_FAILED : forall n m,
  double n = double m ->
  n = m.
Proof.
  intros n m. induction n as [| n' IHn'].
  - (* n = O *) simpl. intros eq. destruct m as [| m'] eqn:E.
    + (* m = O *) reflexivity.
    + (* m = S m' *) discriminate eq.
  - (* n = S n' *) intros eq. destruct m as [| m'] eqn:E.
    + (* m = O *) discriminate eq.
    + (* m = S m' *) f_equal.
Abort.


Theorem double_injective : forall n m,
  double n = double m ->
  n = m.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* n = O *) simpl. intros m eq. destruct m as [| m'] eqn:E.
    + (* m = O *) reflexivity.
    + (* m = S m' *) discriminate eq.
  - (* n = S n' *) intros m eq. destruct m as [| m'] eqn:E.
    + (* m = O *) discriminate eq.
    + (* m = S m' *) f_equal.
      apply IHn'. simpl in eq. injection eq as goal. apply goal. Qed.


(* Exercise: eqb_true *)

Theorem eqb_true : forall n m,
  n =? m = true -> n = m.
Proof.
  intros n. induction n as [| n' IHn'].
  - intros m H. destruct m as [| m'] eqn:E.
    + reflexivity.
    + discriminate H.
  - intros m H. destruct m as [| m'] eqn:E.
    + discriminate H.
    + apply IHn' in H. f_equal. apply H. Qed.
(* Exercise end *)

(* Exercise: eqb_true_informal *)
(* 
Theorem: For any natural numbers n and m,
  n =? m = true -> n = m. 
Proof:
  We will prove this theorem by induction on n.
  - First, suppose n = 0.
    - We must show that 0 =? m = true -> 0 = m.
    - If m = 0, then 0 =? 0 = true, and 0 = 0 holds.
    - If m = S m' for some m', then 0 =? S m' = false, which contradicts the assumption.
    - Therefore, if 0 =? m = true, then m must be 0.
  - Next, suppose n = S n' for some n' and assume the induction hypothesis: 
    for any m, n' =? m = true -> n' = m.
    - We must show that S n' =? m = true -> S n' = m.
    - If m = 0, then S n' =? 0 = false, which contradicts the assumption.
    - If m = S m' for some m', then S n' =? S m' = true if and only if n' =? m' = true.
    - By the induction hypothesis, n' =? m' = true implies n' = m'.
    - Therefore, S n' = S m'.
  - By induction, the theorem holds for all natural numbers n and m.
*)
Definition manual_grade_for_informal_proof : option (nat*string) := None.

(* Exercise end *)

(* Exercise: plus_n_n_injective *)

Theorem plus_n_n_injective : forall n m,
  n + n = m + m ->
  n = m.
Proof.
  intros n. induction n as [| n' IHn'].
  - intros m H. destruct m as [| m'] eqn:E.
    + reflexivity.
    + discriminate H.
  - intros m H. destruct m as [| m'] eqn:E.
    + discriminate H.
    + {
      simpl in H. 
      injection H as H1. 
      apply f_equal.
      apply IHn'.
      rewrite <- plus_n_Sm in H1.
      rewrite <- plus_n_Sm in H1.
      injection H1 as H2.
      apply H2. 
    }
Qed.
(* Exercise end *)

(* Varying the Induction Hypothesis *)
Theorem double_injective_take2_FAILED : forall n m,
  double n = double m ->
  n = m.
Proof.
  intros n m. induction m as [| m' IHm'].
  - (* m = O *) simpl. intros eq. destruct n as [| n'] eqn:E.
    + (* n = O *) reflexivity.
    + (* n = S n' *) discriminate eq.
  - (* m = S m' *) intros eq. destruct n as [| n'] eqn:E.
    + (* n = O *) discriminate eq.
    + (* n = S n' *) f_equal.
        (* We are stuck here, just like before. *)
Abort.
  

(* first introduce all the quantified variables and then re-generalize 
one or more of them, selectively taking variables out of the context 
and putting them back at the beginning of the goal *)
Theorem double_injective_take2 : forall n m,
  double n = double m ->
  n = m.
Proof.
  intros n m.
  (* n and m are both in the context *)
  generalize dependent n.
  (* Now n is back in the goal and we can do induction on
     m and get a sufficiently general IH. *)
  induction m as [| m' IHm'].
  - (* m = O *) simpl. intros n eq. destruct n as [| n'] eqn:E.
    + (* n = O *) reflexivity.
    + (* n = S n' *) discriminate eq.
  - (* m = S m' *) intros n eq. destruct n as [| n'] eqn:E.
    + (* n = O *) discriminate eq.
    + (* n = S n' *) f_equal.
      apply IHm'. injection eq as goal. apply goal. Qed.


(* Exercise: gen_dep_practice *)

Theorem nth_error_after_last: forall (n : nat) (X : Type) (l : list X),
  length l = n ->
  nth_error l n = None.
Proof.
  intros n X l.
  generalize dependent n.
  induction l as [| h t IHt].
  - intros n H. simpl in H. rewrite <- H. reflexivity.
  - intros n H. destruct n as [| n'] eqn:E.
    + discriminate H.
    + simpl in H. injection H as H1. apply IHt. apply H1. Qed.
(* Exercise end *)

(* Unfolding Definitions *)
Definition square n := n * n.
Lemma square_mult : forall n m, square (n * m) = square n * square m.
Proof.
  intros n m.
  simpl.
  unfold square.
  rewrite mult_assoc.
  assert (H : n * m * n = n * n * m).
    { rewrite mul_comm. apply mult_assoc. }
  rewrite H. rewrite mult_assoc. reflexivity.
Qed.

Definition foo (x: nat) := 5.

Fact silly_fact_1 : forall m, foo m + 1 = foo (m + 1) + 1.
Proof.
  intros m.
  simpl.
  reflexivity.
Qed.

Definition bar x :=
  match x with
  | O => 5
  | S _ => 5
  end.
  
Fact silly_fact_2_FAILED : forall m, bar m + 1 = bar (m + 1) + 1.
Proof.
  intros m.
  simpl. (* Does nothing! *)
Abort.

Fact silly_fact_2 : forall m, bar m + 1 = bar (m + 1) + 1.
Proof.
  intros m.
  destruct m eqn:E.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Fact silly_fact_2' : forall m, bar m + 1 = bar (m + 1) + 1.
Proof.
  intros m.
  unfold bar.
  destruct m eqn:E.
  - reflexivity.
  - reflexivity.
Qed.


(* Using destruct on Compound Expressions *)

Definition sillyfun (n : nat) : bool :=
  if n =? 3 then false
  else if n =? 5 then false
  else false.
Theorem sillyfun_false : forall (n : nat),
  sillyfun n = false.
Proof.
  intros n. unfold sillyfun.
  destruct (n =? 3) eqn:E1.
    - (* n =? 3 = true *) reflexivity.
    - (* n =? 3 = false *) destruct (n =? 5) eqn:E2.
      + (* n =? 5 = true *) reflexivity.
      + (* n =? 5 = false *) reflexivity. Qed.


(* Exercise: combine_split *)
Fixpoint split {X Y : Type} (l : list (X*Y))
               : (list X) * (list Y) :=
  match l with
  | [] => ([], [])
  | (x, y) :: t =>
      match split t with
      | (lx, ly) => (x :: lx, y :: ly)
      end
  end.

Theorem combine_split : forall X Y (l : list (X * Y)) l1 l2,
  split l = (l1, l2) ->
  combine l1 l2 = l.
Proof.
  intros X Y l.
  induction l as [| [x y] t IHt].
  - intros l1 l2 H. injection H as H1 H2. rewrite <- H1. rewrite <- H2. reflexivity.
  - intros l1 l2 H. simpl in H. destruct (split t) as [lx ly] eqn:E.
    injection H as H1 H2. rewrite <- H1. rewrite <- H2. simpl. apply f_equal. apply IHt. reflexivity. Qed.
(* Exercise end *)


Definition sillyfun1 (n : nat) : bool :=
  if n =? 3 then true
  else if n =? 5 then true
  else false.

Theorem sillyfun1_odd_FAILED : forall (n : nat),
  sillyfun1 n = true ->
  odd n = true.
Proof.
  intros n eq. unfold sillyfun1 in eq.
  destruct (n =? 3).
  (* stuck... *)
Abort.

Theorem sillyfun1_odd : forall (n : nat),
  sillyfun1 n = true ->
  odd n = true.
Proof.
  intros n eq. unfold sillyfun1 in eq.
  destruct (n =? 3) eqn:Heqe3.
  - (* e3 = true *) apply eqb_true in Heqe3.
    rewrite -> Heqe3. reflexivity.
  - (* e3 = false *)
     destruct (n =? 5) eqn:Heqe5.
        + (* e5 = true *)
          apply eqb_true in Heqe5.
          rewrite -> Heqe5. reflexivity.
        + (* e5 = false *) discriminate eq. Qed.

(* Exercise: destruct_eqn_practice *)

Theorem bool_fn_applied_thrice :
  forall (f : bool -> bool) (b : bool),
  f (f (f b)) = f b.
Proof.
  intros f b.
  destruct (f true) eqn:E1.
  - destruct (f false) eqn:E2.
    + destruct b eqn:E3.
      * rewrite E1. rewrite E1. rewrite E1. reflexivity.
      * rewrite E2. rewrite E1. rewrite E1. reflexivity.
    + destruct b eqn:E3.
      * rewrite E1. rewrite E1. rewrite E1. reflexivity.
      * rewrite E2. rewrite E2. rewrite E2. reflexivity.
  - destruct (f false) eqn:E2.
    + destruct b eqn:E3.
      * rewrite E1. rewrite E2. rewrite E1. reflexivity.
      * rewrite E2. rewrite E1. rewrite E2. reflexivity.
    + destruct b eqn:E3.
      * rewrite E1. rewrite E2. rewrite E2. reflexivity.
      * rewrite E2. rewrite E2. rewrite E2. reflexivity. Qed.
(* Exercise end *)

(* Additional Exercises *)

(* Exercise: eqb_sym *)

Theorem eqb_sym : forall (n m : nat),
  (n =? m) = (m =? n).
Proof.
  intros n m.
  destruct (n =? m) eqn:E.
  - apply eqb_true in E. rewrite E. symmetry. apply eqb_refl.
  - generalize dependent m.
    induction n.
    + destruct m.
      * intros E. discriminate E.
      * reflexivity.
    + destruct m.
      * reflexivity.
      * intros E. simpl in E. apply IHn in E. simpl. rewrite <- E. reflexivity.
Qed.
(* Exercise end *)

(* Exercise: eqb_sym_informal *)

(* 
Theorem: For any natural numbers n and m, (n =? m) = (m =? n).

Proof:
We will prove this theorem by induction on n.

- First, suppose n = 0.
  - We must show that (0 =? m) = (m =? 0).
  - If m = 0, then both sides of the equation are true.
  - If m = S m' for some m', then both sides of the equation are false.
  - Therefore, (0 =? m) = (m =? 0) holds for all m.

- Next, suppose n = S n' for some n' and assume the induction hypothesis: 
  for any m, (n' =? m) = (m =? n').
  - We must show that (S n' =? m) = (m =? S n').
  - If m = 0, then both sides of the equation are false.
  - If m = S m' for some m', then (S n' =? S m') = (n' =? m') by definition of eqb.
  - By the induction hypothesis, (n' =? m') = (m' =? n').
  - Therefore, (S n' =? m) = (m =? S n') holds for all m.

- By induction, the theorem holds for all natural numbers n and m.
*)

(* Exercise end *)


(* Exercise: eqb_trans *)

Theorem eqb_trans : forall n m p,
  n =? m = true ->
  m =? p = true ->
  n =? p = true.
Proof.
  intros n m p H1 H2.
  apply eqb_true in H1.
  apply eqb_true in H2.
  rewrite H1. rewrite H2. apply eqb_refl. Qed.
(* Exercise end *)

(* Exercise: split_combine *)

Definition split_combine_statement : Prop :=
  (* (": Prop" means that we are giving a name to a
     logical proposition here.) *)
  forall X Y (l1: list X) (l2: list Y), 
  length l1 = length l2 -> split (combine l1 l2) = (l1, l2).
Theorem split_combine : split_combine_statement.
Proof.
  intros X Y l1.
  induction l1 as [| h1 t1 IHt1].
  - intros l2 H. destruct l2.
    + reflexivity.
    + discriminate H.
  - intros l2 H. destruct l2.
    + discriminate H.
    + simpl in H. injection H as H1. apply IHt1 in H1. simpl. rewrite H1. reflexivity. Qed.
(* Exercise end *)

(* Exercise: filter_exercise *)
(* Do not modify the following line: *)
Definition manual_grade_for_split_combine : option (nat*string) := None.

(* Exercise: filter_exercise *)
Theorem filter_exercise : forall (X : Type) (test : X -> bool)
                                 (x : X) (l lf : list X),
  filter test l = x :: lf ->
  test x = true.
Proof.
  intros X test x l.
  induction l as [| h t IHt].
  - intros lf H. discriminate H.
  - intros lf H. simpl in H. destruct (test h) eqn:E.
    + injection H as H1 H2. rewrite H1 in E. apply E.
    + apply IHt in H. apply H. Qed.
(* Exercise end *)

(* Exercise: forall_exists_challenge *)

Fixpoint forallb {X : Type} (test : X -> bool) (l : list X) : bool :=
  match l with
  | [] => true
  | h :: t => andb (test h) (forallb test t)
  end.
Example test_forallb_1 : forallb odd [1;3;5;7;9] = true.
Proof. reflexivity. Qed.
Example test_forallb_2 : forallb negb [false;false] = true.
Proof. reflexivity. Qed.
Example test_forallb_3 : forallb even [0;2;4;5] = false.
Proof. reflexivity. Qed.
Example test_forallb_4 : forallb (eqb 5) [] = true.
Proof. reflexivity. Qed.
Fixpoint existsb {X : Type} (test : X -> bool) (l : list X) : bool :=
  match l with
  | [] => false
  | h :: t => orb (test h) (existsb test t)
  end.
Example test_existsb_1 : existsb (eqb 5) [0;2;3;6] = false.
Proof. reflexivity. Qed.
Example test_existsb_2 : existsb (andb true) [true;true;false] = true.
Proof. reflexivity. Qed.
Example test_existsb_3 : existsb odd [1;0;0;0;0;3] = true.
Proof. reflexivity. Qed.
Example test_existsb_4 : existsb even [] = false.
Proof. reflexivity. Qed.

Definition existsb' {X : Type} (test : X -> bool) (l : list X) : bool
  := negb (forallb (fun x => negb (test x)) l).

Theorem existsb_existsb' : forall (X : Type) (test : X -> bool) (l : list X),
  existsb test l = existsb' test l.
Proof.
  intros X test l.
  induction l as [| h t IHt].
  - reflexivity.
  - simpl. 
    destruct (test h) eqn:E.
    + simpl. unfold existsb'. simpl. rewrite E. simpl. reflexivity. 
    + simpl. unfold existsb'. simpl. rewrite E. simpl. apply IHt. Qed.
(* Exercise end *)

(* Using Tactics on Quantified Statements *)




      