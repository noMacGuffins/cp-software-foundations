Require Export Basics.

Print LoadPath.

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
  - (* n = S n' *) simpl. rewrite -> IHn'. reflexivity. Qed.

