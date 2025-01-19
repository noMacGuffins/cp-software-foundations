From LF Require Export Lists.

(* Polymorphism *)

(* Polymorphic Lists *)
Inductive boollist : Type :=
  | bool_nil
  | bool_cons (b : bool) (l : boollist).
(* new inductive datatype for each list *)

Inductive list (X:Type) : Type :=
  | nil
  | cons (x : X) (l : list X).
(* one inductive datatype for all lists *)

(* list is a function from Types to Types *)
Check list : Type -> Type.

(* nil and cons are now polymorphic contructors *)
Check (nil nat) : list nat.
Check (cons nat 3 (nil nat)) : list nat.
Check nil : forall X : Type, list X.
Check cons : forall X : Type, X -> list X -> list X.
Check (cons nat 2 (cons nat 1 (nil nat))) : list nat.

(* polymorphic versions of list-processing functions *)
Fixpoint repeat (X : Type) (x : X) (count : nat) : list X :=
  match count with
  | 0 => nil X
  | S count' => cons X x (repeat X x count')
  end.

Example test_repeat1 :
  repeat nat 4 2 = cons nat 4 (cons nat 4 (nil nat)).
Proof. reflexivity. Qed.

Example test_repeat2 :
  repeat bool false 1 = cons bool false (nil bool).
Proof. reflexivity. Qed.


(* Exercise: mumble_grumble*)

Module MumbleGrumble.
Inductive mumble : Type :=
  | a
  | b (x : mumble) (y : nat)
  | c.
Inductive grumble (X:Type) : Type :=
  | d (m : mumble)
  | e (x : X).

(* Check d (b a 5) *)
Check d mumble (b a 5).
Check d bool (b a 5).
Check e bool true.
Check e mumble (b c 0).
(* Check e bool (b c 0). *)
Check c.

    (* 
        d (b a 5) no
        d mumble (b a 5) yes
        d bool (b a 5) yes **** d does not use X
        e bool true yes
        e mumble (b c 0) yes **** e uses X
        e bool (b c 0) yes
        c no
    *)

(* FILL IN HERE *)
End MumbleGrumble.
(* Exercise end *)


(* Type Annotation Inference *)

Fixpoint repeat' X x count : list X :=
  match count with
  | 0 => nil X
  | S count' => cons X x (repeat' X x count')
  end.

Check repeat'
  : forall X : Type, X -> nat -> list X.
Check repeat
  : forall X : Type, X -> nat -> list X.
(* repeat' has exactly the same type as repeat; coq used type inference to 
deduce the types of X x and count *)


(* Type Argument Inference with Holes *)

Fixpoint repeat'' X x count : list X :=
  match count with
  | 0 => nil _
  | S count' => cons _ x (repeat'' _ x count')
  end.
Definition list123 :=
  cons nat 1 (cons nat 2 (cons nat 3 (nil nat))).
Definition list123' :=
  cons _ 1 (cons _ 2 (cons _ 3 (nil _))).


(* Implicit Arguments *)

Arguments nil {X}.
Arguments cons {X}.
Arguments repeat {X}.
Fixpoint repeat''' {X : Type} (x : X) (count : nat) : list X :=
  match count with
  | 0 => nil
  | S count' => cons x (repeat''' x count')
  end.

Definition list123'' := cons 1 (cons 2 (cons 3 nil)).

(* marking the parameter of an inductive type as implicit causes it to 
become implicit for the type itself, not just for its constructors  *)
Inductive list' {X:Type} : Type :=
  | nil'
  | cons' (x : X) (l : list').


Fixpoint app {X : Type} (l1 l2 : list X) : list X :=
  match l1 with
  | nil => l2
  | cons h t => cons h (app t l2)
  end.
Fixpoint rev {X:Type} (l:list X) : list X :=
  match l with
  | nil => nil
  | cons h t => app (rev t) (cons h nil)
  end.
Fixpoint length {X : Type} (l : list X) : nat :=
  match l with
  | nil => 0
  | cons _ l' => S (length l')
  end.
Example test_rev1 :
  rev (cons 1 (cons 2 nil)) = (cons 2 (cons 1 nil)).
Proof. reflexivity. Qed.
Example test_rev2:
  rev (cons true nil) = cons true nil.
Proof. reflexivity. Qed.
Example test_length1: length (cons 1 (cons 2 (cons 3 nil))) = 3.
Proof. reflexivity. Qed.

(* Supplying Arguments Explicitly *)
Fail Definition mynil := nil.
Definition mynil : list nat := nil.
(* force explicit *)
Check @nil : forall X : Type, list X.
Definition mynil' := @nil nat.

(* Since we have made the constructor type arguments implicit, 
Coq will know to automatically infer these when we use the notations. *)
Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                     (at level 60, right associativity).

Definition list123''' := [1; 2; 3].


(* poly_exercises *)
Theorem app_nil_r : forall (X:Type), forall l:list X,
  l ++ [] = l.
Proof.
  intros.
  induction l as [| n l' IHl'].
  - reflexivity.
  - simpl. rewrite -> IHl'. reflexivity.
Qed.
Theorem app_assoc : forall A (l m n:list A),
  l ++ m ++ n = (l ++ m) ++ n.
Proof.
  intros.
  induction l as [| n' l' IHl'].
  - reflexivity.
  - simpl. rewrite -> IHl'. reflexivity.
Qed.
Lemma app_length : forall (X:Type) (l1 l2 : list X),
  length (l1 ++ l2) = length l1 + length l2.
Proof.
  intros.
  induction l1 as [| n l1' IHl1'].
    - reflexivity.
    - simpl. rewrite -> IHl1'. reflexivity.
Qed.
(* Exercise end *)

(* Exercise: more_poly_exercises *)
Theorem rev_app_distr: forall X (l1 l2 : list X),
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
    intros.
    induction l1 as [| n l1' IHl1'].
    - simpl. rewrite -> app_nil_r. reflexivity.
    - simpl. rewrite -> IHl1'. rewrite -> app_assoc. reflexivity.
Qed.
Theorem rev_involutive : forall X : Type, forall l : list X,
  rev (rev l) = l.
Proof.
    intros.
    induction l as [| n l' IHl'].
    - reflexivity.
    - simpl. rewrite -> rev_app_distr. rewrite -> IHl'. simpl. reflexivity.
(* Exercise end *)







