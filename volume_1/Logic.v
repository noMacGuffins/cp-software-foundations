From LF Require Export Tactics.
(* any statement we might try to prove in Coq has a type, 
namely Prop, the type of propositions *)
Check (forall n m : nat, n + m = m + n) : Prop.

Check 2 = 2 : Prop.
Check 3 = 2 : Prop.
Check forall n : nat, n = 2 : Prop.


Theorem plus_2_2_is_4 :
  2 + 2 = 4.
Proof. reflexivity. Qed.

Definition plus_claim : Prop := 2 + 2 = 4.
Check plus_claim : Prop.

Theorem plus_claim_is_true :
  plus_claim.
Proof. reflexivity. Qed.

(* parametized propositions *)
Definition is_three (n : nat) : Prop :=
  n = 3.
Check is_three : nat -> Prop.

Definition injective {A B} (f : A -> B) : Prop :=
  forall x y : A, f x = f y -> x = y.
Lemma succ_inj : injective S.
Proof.
  intros x y H. injection H as H1. apply H1.
Qed.

(* equals is also a prop *)
Check @eq : forall A : Type, A -> A -> Prop.


(* Logical Connectives *)
Example and_example : 3 + 4 = 7 /\ 2 * 2 = 4.
Proof.
  split.
  - (* 3 + 4 = 7 *) reflexivity.
  - (* 2 * 2 = 4 *) reflexivity.
Qed.

Check @conj : forall A B : Prop, A -> B -> A /\ B.

Example and_example' : 3 + 4 = 7 /\ 2 * 2 = 4.
Proof.
  apply conj.
  - (* 3 + 4 = 7 *) reflexivity.
  - (* 2 + 2 = 4 *) reflexivity.
Qed.


(* Exercise: plus_is_O *)

Example plus_is_O :
  forall n m : nat, n + m = 0 -> n = 0 /\ m = 0.
Proof.
    intros n m H.
    destruct n as [| n'] eqn:E.
    - split.
        + reflexivity.
        + rewrite <- H. reflexivity.
    - split.
        + discriminate.
        + discriminate.
Qed.

(* Exercise end *)

Lemma and_example2 :
  forall n m : nat, n = 0 /\ m = 0 -> n + m = 0.
Proof.
  (* WORKED IN CLASS *)
  intros n m H.
  destruct H as [Hn Hm].
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed.

Lemma and_example2':
  forall n m : nat, n = 0 /\ m = 0 -> n + m = 0.
Proof.
  intros n m [Hn Hm].
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed.

Lemma and_example2'':
  forall n m : nat, n = 0 -> m = 0 -> n + m = 0.
Proof.
  intros n m Hn Hm.
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed.

Lemma and_example3 :
  forall n m : nat, n + m = 0 -> n * m = 0.
Proof.
  (* WORKED IN CLASS *)
  intros n m H.
  apply plus_is_O in H.
  destruct H as [Hn Hm].
  rewrite Hn. reflexivity.
Qed.

Lemma proj1 : forall P Q : Prop,
  P /\ Q -> P.
Proof.
  intros P Q HPQ.
  destruct HPQ as [HP _].
  apply HP. Qed.


(* Exercise: proj2 *)

Lemma proj2 : forall P Q : Prop,
  P /\ Q -> Q.
Proof.
    intros P Q HPQ.
    destruct HPQ as [_ HQ].
    apply HQ. Qed.
    
(* Exercise end *)

Theorem and_commut : forall P Q : Prop,
  P /\ Q -> Q /\ P.
Proof.
  intros P Q [HP HQ].
  split.
    - (* left *) apply HQ.
    - (* right *) apply HP. Qed.

(* Exercise: and_assoc *)
Theorem and_assoc : forall P Q R : Prop,
  P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros P Q R [HP [HQ HR]].
  split.
    - split.
        + apply HP.
        + apply HQ.
    - apply HR. Qed.

(* Exercise end *)

Check and : Prop -> Prop -> Prop.


(* Disjunction *)
Lemma factor_is_O:
  forall n m : nat, n = 0 \/ m = 0 -> n * m = 0.
Proof.
  (* This pattern implicitly does case analysis on
     n = 0 ∨ m = 0 *)
  intros n m [Hn | Hm].
  - (* Here, n = 0 *)
    rewrite Hn. reflexivity.
  - (* Here, m = 0 *)
    rewrite Hm. rewrite <- mult_n_O.
    reflexivity.
Qed.


Lemma or_intro_l : forall A B : Prop, A -> A \/ B.
Proof.
  intros A B HA.
  left.
  apply HA.
Qed.

Lemma zero_or_succ :
  forall n : nat, n = 0 \/ n = S (pred n).
Proof.
  (* WORKED IN CLASS *)
  intros [|n'].
  - left. reflexivity.
  - right. reflexivity.
Qed.


(* Exercise: mult_is_O *)
Lemma mult_is_O :
  forall n m, n * m = 0 -> n = 0 \/ m = 0.
Proof.
    intros n m H.
    destruct n as [| n'] eqn:E.
    - left. reflexivity.
    - destruct m as [| m'] eqn:F.
        + right. reflexivity.
        + left. discriminate. Qed.

(* Exercise end *)


(* Exercise: or_commut *)

Theorem or_commut : forall P Q : Prop,
  P \/ Q -> Q \/ P.
Proof.
    intros P Q [HP | HQ].
    - right. apply HP.
    - left. apply HQ. Qed.

(* Exercise end *)


(* Falsehood and Negation *)
Definition not (P:Prop) := P -> False.
Check not : Prop -> Prop.
Notation "~ x" := (not x) : type_scope.

Theorem ex_falso_quodlibet : forall (P:Prop),
  False -> P.
Proof.
  (* WORKED IN CLASS *)
  intros P contra.
  destruct contra. Qed.


(* Exercise: not_implies_our_not *)

Theorem not_implies_our_not : forall (P:Prop),
  ~ P -> (forall (Q:Prop), P -> Q).
Proof.
    intros P H Q HP.
    unfold not in H.
    destruct H.
    apply HP. Qed.

(* Exercise end *)

Notation "x <> y" := (~(x = y)) : type_scope.

Theorem zero_not_one : 0 <> 1.
Proof.
    unfold not.
    intros contra.
    discriminate contra.
Qed.


Theorem not_False :
  ~ False.
Proof.
  unfold not. intros H. destruct H. Qed.

Theorem contradiction_implies_anything : forall P Q : Prop,
  (P /\ ~P) -> Q.
Proof.
  (* WORKED IN CLASS *)
  intros P Q [HP HNP]. unfold not in HNP.
  apply HNP in HP. destruct HP. Qed.
Theorem double_neg : forall P : Prop,
  P -> ~~P.
Proof.
  (* WORKED IN CLASS *)
  intros P H. unfold not. intros G. apply G. apply H. Qed.


(* Exercise: double_neg_informal *)

(* 
Theorem: 
    For any proposition P, P implies ~~P.
Proof:
    To prove that P -> ~~P, we start by assuming P is true. 
    We need to show that ~~P is true, which means showing that (P -> False) -> False.
    Assume (P -> False) is true. This means that P implies a contradiction.
    However, we already assumed that P is true, so we have a contradiction.
    Therefore, (P -> False) must be false, which means ~~P is true.
*)
Definition manual_grade_for_double_neg_inf : option (nat*string) := None.
(* Exercise end *)

(* Exercise: contrapositive *)
Theorem contrapositive : forall (P Q : Prop),
  (P -> Q) -> (~Q -> ~P).
Proof.
    intros P Q H H1 H2.
    unfold not in H1.
    apply H1.
    apply H.
    apply H2. Qed.

(* Exercise end *)

(* Exercise: not_both_true_and_false *)

Theorem not_both_true_and_false : forall P : Prop,
  ~(P /\ ~P).
Proof.
    intros P [HP HNP].
    unfold not in HNP.
    apply HNP.
    apply HP. Qed.
  
(* Exercise end *)

(* Exercise: not_PNP_informal *)
(* 
Theorem:
  For any proposition P, it is not the case that both P and not P are true.
Proof:
  To prove that ~(P /\ ~P), we start by assuming the opposite, that P /\ ~P is true.
  This means that both P is true and ~P (P implies False) is true.
  However, if P is true, then ~P must be false because ~P states that P implies False.
  This creates a contradiction because P cannot be both true and false at the same time.
  Therefore, our initial assumption that P /\ ~P is true must be false.
  Hence, ~(P /\ ~P) is true.
*)
Definition manual_grade_for_not_PNP_informal : option (nat*string) := None.
(* Exercise end *)

(* Exercise: de_morgan_not_or *)
Theorem de_morgan_not_or : forall (P Q : Prop),
    ~ (P \/ Q) -> ~P /\ ~Q.
Proof.
    intros P Q H.
    unfold not in H.
    split.
    - intros HP. apply H. left. apply HP.
    - intros HQ. apply H. right. apply HQ. Qed.

(* Exercise end *)

(* Exercise: not_S_inverse_pred *)

Theorem not_S_inverse_pred : forall n : nat,
  ~ (S n = 0).
Proof.
    unfold not.
    intros n H.
    discriminate H. Qed.

(* Exercise end *)  

Theorem not_true_is_false : forall b : bool,
  b <> true -> b = false.
Proof.
  intros b H. destruct b eqn:HE.
  - (* b = true *)
    unfold not in H.
    apply ex_falso_quodlibet.
    apply H. reflexivity.
  - (* b = false *)
    reflexivity.
Qed.

Theorem not_true_is_false' : forall b : bool,
  b <> true -> b = false.
Proof.
  intros [] H. (* note implicit destruct b here *)
  - (* b = true *)
    unfold not in H.
    exfalso. (* <=== *)
    apply H. reflexivity.
  - (* b = false *) reflexivity.
Qed.

(* Truth *)

Lemma True_is_true : True.
Proof. apply I. Qed.

Definition disc_fn (n: nat) : Prop :=
  match n with
  | O => True
  | S _ => False
  end.
Theorem disc_example : forall n, ~ (O = S n).
Proof.
  intros n contra.
  assert (H : disc_fn O). { simpl. apply I. }
  rewrite contra in H. simpl in H. apply H.
Qed.

(* Exercise: nil_is_not_cons *)

Theorem nil_is_not_cons : forall X (x : X) (xs : list X), ~ (nil = x :: xs).
Proof.
    intros X x xs H.
    discriminate H. Qed.

(* Exercise end *)

(* Logical Equivalence *)
Module IffPlayground.

Definition iff (P Q : Prop) := (P -> Q) /\ (Q -> P).
Notation "P <-> Q" := (iff P Q)
                      (at level 95, no associativity)
                      : type_scope.
End IffPlayground.

Theorem iff_sym : forall P Q : Prop,
  (P <-> Q) -> (Q <-> P).
Proof.
  (* WORKED IN CLASS *)
  intros P Q [HAB HBA].
  split.
  - (* -> *) apply HBA.
  - (* <- *) apply HAB. Qed.
Lemma not_true_iff_false : forall b,
  b <> true <-> b = false.
Proof.
  (* WORKED IN CLASS *)
  intros b. split.
  - (* -> *) apply not_true_is_false.
  - (* <- *)
    intros H. rewrite H. intros H'. discriminate H'.
Qed.

Lemma apply_iff_example1:
  forall P Q R : Prop, (P <-> Q) -> (Q -> R) -> (P -> R).
Proof.
  intros P Q R Hiff H HP. apply H. apply Hiff. apply HP.
Qed.
Lemma apply_iff_example2:
  forall P Q R : Prop, (P <-> Q) -> (P -> R) -> (Q -> R).
Proof.
  intros P Q R Hiff H HQ. apply H. apply Hiff. apply HQ.
Qed.


(* Exercise: iff_properties *)
Theorem iff_refl : forall P : Prop,
  P <-> P.
Proof.
    intros P. 
    split.
    - intros HP. apply HP.
    - intros HP. apply HP. Qed.

Theorem iff_trans : forall P Q R : Prop,
  (P <-> Q) -> (Q <-> R) -> (P <-> R).
Proof.
    intros P Q R [HPQ HQP] [HQR HRQ].
    split.
    - intros HP. apply HQR. apply HPQ. apply HP.
    - intros HR. apply HQP. apply HRQ. apply HR. Qed.

(* Exercise end *)

(* Exercise: or_distributes_over_and *)

Theorem or_distributes_over_and : forall P Q R : Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
    intros P Q R.
    split.
    - intros [HP | [HQ HR]].
        + split.
            * left. apply HP.
            * left. apply HP.
        + split.
            * right. apply HQ.
            * right. apply HR.
    - intros [[HP | HQ] [HP' | HR]].
        + left. apply HP.
        + left. apply HP.
        + left. apply HP'.
        + right. split.
            * apply HQ.
            * apply HR. Qed.

(* Exercise end *)

(* Exercise: Setoids and Logical Equivalence *)

From Coq Require Import Setoids.Setoid.

Lemma mul_eq_0 : forall n m, n * m = 0 <-> n = 0 \/ m = 0.
Proof.
  split.
  - apply mult_is_O.
  - apply factor_is_O.
Qed.

Theorem or_assoc :
  forall P Q R : Prop, P \/ (Q \/ R) <-> (P \/ Q) \/ R.
Proof.
  intros P Q R. split.
  - intros [H | [H | H]].
    + left. left. apply H.
    + left. right. apply H.
    + right. apply H.
  - intros [[H | H] | H].
    + left. apply H.
    + right. left. apply H.
    + right. right. apply H.
Qed.

Lemma mul_eq_0_ternary :
  forall n m p, n * m * p = 0 <-> n = 0 \/ m = 0 \/ p = 0.
Proof.
  intros n m p.
  rewrite mul_eq_0. rewrite mul_eq_0. rewrite or_assoc.
  reflexivity.
Qed.


(* Existential Quantification *)

Definition Even x := exists n : nat, x = double n.

Lemma four_is_Even : Even 4.
Proof.
  unfold Even. exists 2. reflexivity.
Qed.

Theorem exists_example_2 : forall n,
  (exists m, n = 4 + m) ->
  (exists o, n = 2 + o).
Proof.
  (* WORKED IN CLASS *)
  intros n [m Hm]. (* note implicit [destruct] here *)
  exists (2 + m).
  apply Hm.  Qed.

(* Exercise: dist_not_exists *)
Theorem dist_not_exists : forall (X:Type) (P : X -> Prop),
  (forall x, P x) -> ~ (exists x, ~ P x).
Proof.
    intros X P H [x H1].
    unfold not in H1.
    apply H1.
    apply H. Qed.

(* Exercise end *)

(* Exercise: dist_exists_or *)
Theorem dist_exists_or : forall (X:Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
    intros X P Q.
    split.
    - intros [x [HP | HQ]].
        + left. exists x. apply HP.
        + right. exists x. apply HQ.
    - intros [[x HP] | [x HQ]].
        + exists x. left. apply HP.
        + exists x. right. apply HQ. Qed.

(* Exercise end *)

(* Exercise: leb_plus_exists *)

Theorem leb_plus_exists : forall n m, n <=? m = true -> exists x, m = n+x.
Proof.
  induction n.
  - intros. exists m. reflexivity.
  - destruct m.
    + intros. exists 0. simpl. discriminate.
    + intros. apply IHn in H. destruct H. rewrite H. exists x. reflexivity.
Qed.
Theorem plus_exists_leb : forall n m, (exists x, m = n+x) -> n <=? m = true.
Proof.
  intros.
  destruct H.
  generalize dependent m.
  induction n.
  - reflexivity.
  - intros. destruct m.
    + discriminate H.
    + rewrite add_comm in H. 
      rewrite <- plus_n_Sm in H.
      injection H as H.  
      rewrite add_comm in H.
      apply IHn in H.
      simpl.
      apply H.
Qed.
(* Exercise end *)

(* Programming with Propositions *)
Fixpoint In {A : Type} (x : A) (l : list A) : Prop :=
  match l with
  | [] => False
  | x' :: l' => x' = x \/ In x l'
  end.

Example In_example_1 : In 4 [1; 2; 3; 4; 5].
Proof.
  (* WORKED IN CLASS *)
  simpl. right. right. right. left. reflexivity.
Qed.

Example In_example_2 :
  forall n, In n [2; 4] ->
  exists n', n = 2 * n'.
Proof.
  (* WORKED IN CLASS *)
  simpl.
  intros n [H | [H | []]].
  - exists 1. rewrite <- H. reflexivity.
  - exists 2. rewrite <- H. reflexivity.
Qed.

Theorem In_map :
  forall (A B : Type) (f : A -> B) (l : list A) (x : A),
         In x l ->
         In (f x) (map f l).
Proof.
  intros A B f l x.
  induction l as [|x' l' IHl'].
  - (* l = nil, contradiction *)
    simpl. intros [].
  - (* l = x' :: l' *)
    simpl. intros [H | H].
    + rewrite H. left. reflexivity.
    + right. apply IHl'. apply H.
Qed.


(* Exercise: In_map_iff *)

Lemma In_map_iff : forall (A B : Type) (f : A -> B) (l : list A) (y : B),
  In y (map f l) <-> exists x, f x = y /\ In x l.
Proof.
  intros A B f l y. split.
  - induction l as [|x l' IHl'].
    + simpl. intros. contradiction.
    + simpl. intros [H | H].
        * exists x. split.
            { apply H. }
            { left. reflexivity. }
        * apply IHl' in H. destruct H as [x' [H1 H2]]. exists x'. split.
            { apply H1. }
            { right. apply H2. }
  - induction l as [|x l' IHl'].
    + simpl. intros [x0 [H1 H2]]. contradiction.
    + simpl. intros [x1 [H1 H2]]. destruct H2.
        * left. rewrite H. apply H1.
        * right. apply IHl'. exists x1. split.
            { rewrite H1. reflexivity. }
            { apply H. }
Qed.

(* Exercise end *)

(* Exercise: In_app_iff *)
Theorem In_app_iff : forall A l l' (a:A),
  In a (l++l') <-> In a l \/ In a l'.
Proof.
  intros A l. induction l as [|a' l' IH].
  - simpl. intros. split.
    + intros. right. apply H.
    + intros [H | H].
      * contradiction.
      * apply H.
  - split.
    + intros [H | H].
      * left. left. apply H.
      * apply IH in H. destruct H.
          { left. right. apply H. }
          { right. apply H. }
    + intros [H | H].
      * destruct H.
          { left. apply H. }
          { right. apply IH. left. apply H. }
      * right. apply IH. right. apply H.
Qed.

(* Exercise: All *)
Fixpoint All {T : Type} (P : T -> Prop) (l : list T) : Prop
  := match l with
     | [] => True
     | (x :: l') => P x /\ All P l'
     end.

Theorem All_In :
  forall T (P : T -> Prop) (l : list T),
    (forall x, In x l -> P x) <->
    All P l.
Proof.
    intros T P l. split.
    - induction l as [| x l' IHl'].
        + simpl. intros _. apply I.
        + simpl.
          { 
            split.
            - apply H. left. reflexivity.
            - apply IHl'. intros. apply H. right. apply H0. 
          }
    - induction l as [| x l' IHl'].
        + simpl. intros _. intros x H. contradiction.
        + simpl. intros [H1 H2] x0 [H3 | H4].
            { rewrite <- H3. apply H1. }
            { apply IHl'. apply H2. apply H4. }
Qed.

(* Exercise end *)

(* Exercise: combine_odd_even *)

Definition combine_odd_even (Podd Peven : nat -> Prop) : nat -> Prop := 
fun n => if odd n then Podd n else Peven n.

Theorem combine_odd_even_intro :
  forall (Podd Peven : nat -> Prop) (n : nat),
    (odd n = true -> Podd n) ->
    (odd n = false -> Peven n) ->
    combine_odd_even Podd Peven n.
Proof.
    intros Podd Peven n H1 H2.
    unfold combine_odd_even.
    destruct (odd n) eqn:E.
    - apply H1. reflexivity.
    - apply H2. reflexivity. Qed.

Theorem combine_odd_even_elim_odd :
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
    odd n = true ->
    Podd n.
Proof.
    intros Podd Peven n H1 H2.
    unfold combine_odd_even in H1.
    rewrite H2 in H1.
    apply H1. Qed.

Theorem combine_odd_even_elim_even :
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
    odd n = false ->
    Peven n.
Proof.
    intros Podd Peven n H1 H2.
    unfold combine_odd_even in H1.
    rewrite H2 in H1.
    apply H1. Qed.

(* Exercise end *)

(* Applying Theorems to Arguments *)

Check plus : nat -> nat -> nat.
Check @rev : forall X, list X -> list X.

Lemma add_comm3 :
  forall x y z, x + (y + z) = (z + y) + x.
Proof.
  intros x y z.
  rewrite add_comm.
  rewrite add_comm.
  (* We are back where we started... *)
Abort.

Lemma add_comm3_take2 :
  forall x y z, x + (y + z) = (z + y) + x.
Proof.
  intros x y z.
  rewrite add_comm.
  assert (H : y + z = z + y).
    { rewrite add_comm. reflexivity. }
  rewrite H.
  reflexivity.
Qed.

Lemma add_comm3_take3 :
  forall x y z, x + (y + z) = (z + y) + x.
Proof.
  intros x y z.
  rewrite add_comm.
  rewrite (add_comm y z).
  reflexivity.
Qed.

Lemma add_comm3_take4 :
  forall x y z, x + (y + z) = (z + y) + x.
Proof.
  intros x y z.
  rewrite (add_comm x (y + z)).
  rewrite (add_comm y z).
  reflexivity.
Qed.

Theorem in_not_nil :
  forall A (x : A) (l : list A), In x l -> l <> [].
Proof.
  intros A x l H. unfold not. intro Hl.
  rewrite Hl in H.
  simpl in H.
  apply H.
Qed.


Lemma in_not_nil_42 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  Fail apply in_not_nil.
Abort.

(** Use [apply ... with ...] *)
Lemma in_not_nil_42_take2 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  apply in_not_nil with (x := 42).
  apply H.
Qed.

(** Use [apply ... in ...] *)
Lemma in_not_nil_42_take3 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  apply in_not_nil in H.
  apply H.
Qed.

(** Explicitly apply the lemma to the value for [x]. *)
Lemma in_not_nil_42_take4 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  apply (in_not_nil nat 42).
  apply H.
Qed.

(** Explicitly apply the lemma to a hypothesis. *)
Lemma in_not_nil_42_take5 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  apply (in_not_nil _ _ _ H).
Qed.

Example lemma_application_ex :
  forall {n : nat} {ns : list nat},
    In n (map (fun m => m * 0) ns) ->
    n = 0.
Proof.
  intros n ns H.
  destruct (proj1 _ _ (In_map_iff _ _ _ _ _) H)
           as [m [Hm _]].
  rewrite mul_0_r in Hm. rewrite <- Hm. reflexivity.
Qed.

(* Working with Decidable Properties *)

Example even_42_bool : even 42 = true.
Proof. reflexivity. Qed.

Example even_42_prop : Even 42.
Proof. unfold Even. exists 21. reflexivity. Qed.

Lemma even_double : forall k, even (double k) = true.
Proof.
  intros k. induction k as [|k' IHk'].
  - reflexivity.
  - simpl. apply IHk'.
Qed.


(* Exercise: even_double_conv *)
Lemma even_double_conv : forall n, exists k,
  n = if even n then double k else S (double k).
Proof.
  intros n.
  induction n.
  - simpl. exists 0. reflexivity.
  - rewrite even_S. destruct (even n) eqn:E.
      + destruct IHn. exists x. simpl. rewrite H. reflexivity. 
      + destruct IHn. exists (S x). simpl. rewrite <- H. reflexivity. Qed.

(* Exercise end *)

Theorem even_bool_prop : forall n,
  even n = true <-> Even n.
Proof.
  intros n. split.
  - intros H. destruct (even_double_conv n) as [k Hk].
    rewrite Hk. rewrite H. exists k. reflexivity.
  - intros [k Hk]. rewrite Hk. apply even_double.
Qed.

Theorem eqb_eq : forall n1 n2 : nat,
  n1 =? n2 = true <-> n1 = n2.
Proof.
    intros n1 n2. split.
    - apply eqb_true.
    - intros. symmetry. rewrite H. rewrite -> eqb_refl. reflexivity. Qed.

Fail
Definition is_even_prime n :=
  if n = 2 then true
  else false.

Example even_1000 : Even 1000.
Proof. unfold Even. exists 500. reflexivity. Qed.

Example even_1000' : even 1000 = true.
Proof. reflexivity. Qed.

Example even_1000'' : Even 1000.
Proof. apply even_bool_prop. reflexivity. Qed.

Example not_even_1001 : even 1001 = false.
Proof.
  (* WORKED IN CLASS *)
  reflexivity.
Qed.

Example not_even_1001' : ~(Even 1001).
Proof.
  (* WORKED IN CLASS *)
  unfold not.
  rewrite <- even_bool_prop.
  simpl.
  intro H.
  discriminate H.
Qed.

Lemma plus_eqb_example : forall n m p : nat,
  n =? m = true -> n + p =? m + p = true.
Proof.
  (* WORKED IN CLASS *)
  intros n m p H.
    rewrite eqb_eq in H.
  rewrite H.
  rewrite eqb_eq.
  reflexivity.
Qed.

(* Exercise: logical_connectives *)
Theorem andb_true_iff : forall b1 b2:bool,
  b1 && b2 = true <-> b1 = true /\ b2 = true.
Proof.
  intros b1 b2. split.
  - intros H. split.
      + destruct b1.
          { reflexivity. }
          { simpl in H. discriminate. }
      + destruct b2.
          { reflexivity. }
          { 
            destruct b1.
            * discriminate H. 
            * discriminate H. 
          }
  - intros [H1 H2]. rewrite H1. rewrite H2. reflexivity. Qed.

Theorem orb_true_iff : forall b1 b2,
  b1 || b2 = true <-> b1 = true \/ b2 = true.
Proof.
  intros b1 b2. split.
  - intros H. destruct b1.
      + left. reflexivity.
      + simpl in H. destruct b2.
          { right. reflexivity. }
          { discriminate H. }
  - intros [H1 | H2]. 
      + rewrite H1. reflexivity.
      + rewrite H2. destruct b1.
          { reflexivity. }
          { reflexivity. } Qed.

(* Exercise end *)

(* Exercise: eqb_neq *)

Theorem eqb_neq : forall x y : nat,
  x =? y = false <-> x <> y.
Proof.
  intros x y. split.
  - intros H1 H2. rewrite H2 in H1. rewrite eqb_refl in H1.  discriminate H1.
  - intros H. unfold not in H. destruct (x =? y) eqn:E.
      + apply eqb_true in E. apply H in E. destruct E.
      + reflexivity. Qed.

(* Exercise end *)

(* Exercise: eqb_list *)

Fixpoint eqb_list {A : Type} (eqb : A -> A -> bool)
                  (l1 l2 : list A) : bool :=
  match l1, l2 with
  | [], [] => true
  | [], _ :: _ => false
  | _ :: _, [] => false
  | x :: l1', y :: l2' => eqb x y && eqb_list eqb l1' l2'
  end.
  
Theorem eqb_list_true_iff :
  forall A (eqb : A -> A -> bool),
    (forall a1 a2, eqb a1 a2 = true <-> a1 = a2) ->
    forall l1 l2, eqb_list eqb l1 l2 = true <-> l1 = l2.
Proof.
    intros A eqb H l1 l2. split.
    - generalize dependent l2. induction l1 as [| x l1' IHl1'].
        + destruct l2.
            { reflexivity. }
            { simpl. intros. discriminate. }
        + destruct l2.
            { simpl. intros. discriminate. }
            { simpl. intros. apply andb_true_iff in H0. destruct H0 as [H1 H2].
                apply H in H1. rewrite H1. apply IHl1' in H2. rewrite H2. reflexivity. }
    - generalize dependent l2. induction l1 as [| x l1' IHl1'].
        + destruct l2.
            { reflexivity. }
            { simpl. intros. discriminate. }
        + destruct l2.
            { simpl. intros. discriminate. }
            { simpl. intros. injection H0 as H1 H2. apply H in H1. rewrite H1. apply IHl1' in H2. rewrite H2. reflexivity. } 
Qed.

(* Exercise end *)

(* Exercise: All_forallb *)
Fixpoint forallb {X : Type} (test : X -> bool) (l : list X) : bool :=
  match l with
  | [] => true
  | x :: l' => andb (test x) (forallb test l')
  end.
Theorem forallb_true_iff : forall X test (l : list X),
  forallb test l = true <-> All (fun x => test x = true) l.
Proof.
  intros X test l. split.
  - induction l as [| x l' IHl'].
      + simpl. intros _. apply I.
      + simpl. intros H. apply andb_true_iff in H. destruct H as [H1 H2]. split.
          { apply H1. }
          { apply IHl'. apply H2. }
  - induction l as [| x l' IHl'].
      + simpl. intros _. reflexivity.
      + simpl. intros [H1 H2]. apply andb_true_iff. split.
          { apply H1. }
          { apply IHl'. apply H2. } Qed.

(* Exercise end *)

(* The Logic of Coq *)

Example function_equality_ex1 :
  (fun x => 3 + x) = (fun x => (pred 4) + x).
Proof. reflexivity. Qed.

Example function_equality_ex2 :
  (fun x => plus x 1) = (fun x => plus 1 x).
Proof.
  Fail reflexivity. Fail rewrite add_comm.
  (* Stuck *)
Abort.

(* Axiom has the same effect as a theorem with an admitted 
but tells the readers that it will not be proved later *)
Axiom functional_extensionality : forall {X Y: Type}
                                    {f g : X -> Y},
  (forall (x:X), f x = g x) -> f = g.

Example function_equality_ex2 :
  (fun x => plus x 1) = (fun x => plus 1 x).
Proof.
  apply functional_extensionality. intros x.
  apply add_comm.
Qed.

Print Assumptions function_equality_ex2.

(* Exercise: tr_rev_correct *)

Fixpoint rev_append {X} (l1 l2 : list X) : list X :=
  match l1 with
  | [] => l2
  | x :: l1' => rev_append l1' (x :: l2)
  end.
Definition tr_rev {X} (l : list X) : list X :=
  rev_append l [].

Lemma rev_app_nil_r : forall X (l1 l2 : list X), 
rev_append l1 l2 = rev_append l1 [] ++ l2.
Proof.
    intros X l1 l2. 
    generalize dependent l2.
    induction l1 as [| x l1' IHl1'].
    - simpl. reflexivity.
    - simpl. 
      rewrite -> IHl1'. 
      intros l2. 
      rewrite -> (IHl1' (x :: l2)). 
      rewrite <- app_assoc. reflexivity. Qed.


Theorem tr_rev_correct : forall X, @tr_rev X = @rev X.
Proof.
    intros X. 
    apply functional_extensionality. 
    intros l. 
    induction l as [| x l' IHl'].
    - simpl. reflexivity.
    - simpl. rewrite <- IHl'. unfold tr_rev. simpl. apply rev_app_nil_r. Qed.

(* Exercise end *)

(* Classical vs. Constructive Logic *)

Definition excluded_middle := forall P : Prop,
  P \/ ~ P.

Theorem restricted_excluded_middle : forall P b,
  (P <-> b = true) -> P \/ ~ P.
Proof.
  intros P [] H.
  - left. rewrite H. reflexivity.
  - right. unfold not. rewrite H. intros contra. discriminate contra.
Qed.

Theorem restricted_excluded_middle_eq : forall (n m : nat),
  n = m \/ n <> m.
Proof.
  intros n m.
  apply (restricted_excluded_middle (n = m) (n =? m)).
  symmetry.
  apply eqb_eq.
Qed.

(* 
Sadly, this trick only works for decidable propositions.
Logics like Coq's, which do not assume the excluded middle,
are referred to as constructive logics. 
Arguments by contradiction, in particular, 
are infamous for leading to non-constructive proofs
*)

(* Exercise: excluded_middle_irrefutable *)

Theorem excluded_middle_irrefutable: forall (P : Prop),
  ~ ~ (P \/ ~ P).
Proof.
    unfold not.
    intros P H.
    apply H.
    right.
    intros HP.
    apply H.
    left.
    apply HP. Qed.

(* Exercise end *)

(* Exercise: not_exists_dist *)

Theorem not_exists_dist :
  excluded_middle ->
  forall (X:Type) (P : X -> Prop),
    ~ (exists x, ~ P x) -> (forall x, P x).
Proof.
    intros EM X P H x.
    destruct (EM (P x)) as [HP | HNP].
    - apply HP.
    - unfold not in H. apply ex_falso_quodlibet. apply H. exists x. apply HNP. 
Qed.

(* Exercise end *)

(* Exercise: classical_axioms *)

Definition peirce := forall P Q: Prop,
  ((P -> Q) -> P) -> P.

Definition double_negation_elimination := forall P:Prop,
  ~~P -> P.

Definition de_morgan_not_and_not := forall P Q:Prop,
  ~(~P /\ ~Q) -> P \/ Q.

Definition implies_to_or := forall P Q:Prop,
  (P -> Q) -> (~P \/ Q).

Theorem peirce_implies_double_negation_elimination :
  peirce -> double_negation_elimination.
Proof.
    unfold peirce, double_negation_elimination.
    intros H P H1.
    apply H with (Q := False).
    intros H2.
    unfold not in H1.
    exfalso. apply H1. apply H2. 
  Qed.

Theorem double_negation_elimination_implies_de_morgan_not_and_not :
  double_negation_elimination -> de_morgan_not_and_not.
Proof.
    unfold double_negation_elimination, de_morgan_not_and_not.
    unfold not.
    intros.
    apply H. intros. apply H0. split.
    + intros H2. apply or_intro_l with (B:=Q) in H2. apply H1. apply H2.
    + intros H2. apply or_intro_l with (B:=P) in H2. apply or_commut in H2. apply H1. apply H2.
Qed.

Theorem de_morgan_not_and_not_implies_implies_to_or :
  de_morgan_not_and_not -> implies_to_or.
Proof.
    unfold de_morgan_not_and_not, implies_to_or.
    intros H P Q H1.
    apply H.
    intros H2.
    unfold not in H2.
    destruct H2 as [Ha Hb].
    - apply Ha. intros Haa. apply Hb. apply H1. apply Haa.
Qed.

Theorem implies_to_or_implies_excluded_middle :
  implies_to_or -> excluded_middle.
Proof.
    unfold implies_to_or, excluded_middle.
    intros H P.
    apply or_commut. apply H. intros. apply H0. 
  Qed.

Theorem excluded_middle_implies_peirce :
  excluded_middle -> peirce.
Proof.
    unfold excluded_middle, peirce.
    intros H P Q H1.
    destruct (H P) as [HP | HNP].
    - apply HP.
    - apply H1. intros HP. apply ex_falso_quodlibet. apply HNP. apply HP. 
Qed.

(* Exercise end *)

    



