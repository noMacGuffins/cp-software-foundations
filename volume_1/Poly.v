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
Qed.
(* Exercise end *)


(* Polymorphic Pairs *)

Inductive prod (X Y : Type) : Type :=
| pair (x : X) (y : Y).
Arguments pair {X} {Y}.

Notation "( x , y )" := (pair x y).
Notation "X * Y" := (prod X Y) : type_scope.
(* he annotation : type_scope tells Coq that this abbreviation should only be used 
when parsing types, not when parsing expressions. 
This avoids a clash with the multiplication symbol. *)

Definition fst {X Y : Type} (p : X * Y) : X :=
  match p with
  | (x, y) => x
  end.
Definition snd {X Y : Type} (p : X * Y) : Y :=
  match p with
  | (x, y) => y
  end.
Fixpoint combine {X Y : Type} (lx : list X) (ly : list Y)
           : list (X*Y) :=
  match lx, ly with
  | [], _ => []
  | _, [] => []
  | x :: tx, y :: ty => (x, y) :: (combine tx ty)
  end.


(* Exercise: combine_checks *)
(* Type of combine is 
forall X Y: Type, list X -> list Y -> list (X * Y) *)
Check @combine.
(* [(1, false), (2, false)] *)
Compute (combine [1;2] [false;false;true;true]).
(* Exercise end *)

(* Exercise: split *)
Fixpoint split {X Y : Type} (l : list (X*Y)) : (list X) * (list Y) := 
    match l with
        | [] => ([], [])
        | (x, y) :: t => match split t with
                        | (lx, ly) => (x :: lx, y :: ly)
                        end
    end.
Example test_split:
  split [(1,false);(2,false)] = ([1;2],[false;false]).
Proof.
reflexivity.
Qed.
(* Exercise end *)

(* Polymorphic Options *)
Module OptionPlayground.
Inductive option (X:Type) : Type :=
  | Some (x : X)
  | None.
Arguments Some {X}.
Arguments None {X}.
End OptionPlayground.
Fixpoint nth_error {X : Type} (l : list X) (n : nat)
                   : option X :=
  match l with
  | nil => None
  | a :: l' => match n with
               | O => Some a
               | S n' => nth_error l' n'
               end
  end.
Example test_nth_error1 : nth_error [4;5;6;7] 0 = Some 4.
Proof. reflexivity. Qed.
Example test_nth_error2 : nth_error [[1];[2]] 1 = Some [2].
Proof. reflexivity. Qed.
Example test_nth_error3 : nth_error [true] 2 = None.
Proof. reflexivity. Qed.


(* Exercise: hd_error_poly *)
Definition hd_error {X : Type} (l : list X) : option X :=
    match l with
        | [] => None
        | h :: t => Some h
    end.

Check @hd_error : forall X : Type, list X -> option X.

Example test_hd_error1 : hd_error [1;2] = Some 1.
Proof. reflexivity. Qed.

Example test_hd_error2 : hd_error [[1];[2]] = Some [1].
Proof. reflexivity. Qed.
(* Exercise end *)


(* Functions as Data *)

(* High order functions: functions that manipulate other functions *)
Definition doit3times {X : Type} (f : X->X) (n : X) : X :=
  f (f (f n)).
Check @doit3times : forall X : Type, (X -> X) -> X -> X.
Example test_doit3times: doit3times minustwo 9 = 3.
Proof. reflexivity. Qed.

Example test_doit3times': doit3times negb true = false.
Proof. reflexivity. Qed.


(* Filter *)
Fixpoint filter {X:Type} (test: X -> bool) (l:list X) : list X :=
  match l with
  | [] => []
  | h :: t =>
    if test h then h :: (filter test t)
    else filter test t
  end.

Example test_filter1: filter even [1;2;3;4] = [2;4].
Proof. reflexivity. Qed.

Definition length_is_1 {X : Type} (l : list X) : bool :=
  (length l) =? 1.
Example test_filter2:
    filter length_is_1
           [ [1; 2]; [3]; [4]; [5;6;7]; []; [8] ]
  = [ [3]; [4]; [8] ].
Proof. reflexivity. Qed.

Definition countoddmembers' (l:list nat) : nat :=
  length (filter odd l).
Example test_countoddmembers'1: countoddmembers' [1;0;3;1;4;5] = 4.
Proof. reflexivity. Qed.
Example test_countoddmembers'2: countoddmembers' [0;2;4] = 0.
Proof. reflexivity. Qed.
Example test_countoddmembers'3: countoddmembers' nil = 0.
Proof. reflexivity. Qed.

(* Anonymous functions *)
Example test_anon_fun':
  doit3times (fun n => n * n) 2 = 256.
Proof. reflexivity. Qed.

Example test_filter2':
    filter (fun l => (length l) =? 1)
           [ [1; 2]; [3]; [4]; [5;6;7]; []; [8] ]
  = [ [3]; [4]; [8] ].
Proof. reflexivity. Qed.


(* Exercise: filter_even_gt7 *)
Definition filter_even_gt7 (l : list nat) : list nat :=
    filter (fun n => even n && (7 <? n)) l.
Example test_filter_even_gt7_1 :
  filter_even_gt7 [1;2;6;9;10;3;12;8] = [10;12;8].
Proof. reflexivity. Qed.
Example test_filter_even_gt7_2 :
  filter_even_gt7 [5;2;6;19;129] = [].
Proof. reflexivity. Qed.
(* Exercise end *)

(* Exercise: partition *)
Definition partition {X : Type} (test : X -> bool) (l : list X) : list X * list X :=
    (filter test l, filter (fun x => negb (test x)) l).

Example test_partition1: partition odd [1;2;3;4;5] = ([1;3;5], [2;4]).
Proof. reflexivity. Qed.

Example test_partition2: partition (fun x => false) [5;9;0] = ([], [5;9;0]).
Proof. reflexivity. Qed.
(* Exercise end *)

(* Map *)
Fixpoint map {X Y : Type} (f : X->Y) (l : list X) : list Y :=
  match l with
  | [] => []
  | h :: t => (f h) :: (map f t)
  end.

Example test_map1: map (fun x => plus 3 x) [2;0;2] = [5;3;5].
Proof. reflexivity. Qed.

Example test_map2:
  map odd [2;1;2;5] = [false;true;false;true].
Proof. reflexivity. Qed.

Example test_map3:
    map (fun n => [even n;odd n]) [2;1;2;5]
  = [[true;false];[false;true];[true;false];[false;true]].
Proof. reflexivity. Qed.

(* Exercise: map_rev *)
Lemma app_map : forall (X Y : Type) (f : X -> Y) (l : list X) (x : X),
  app (map f l) [f x] = map f (app l [x]).
Proof.
  intros.
  induction l.
  - reflexivity.
  - simpl. rewrite -> IHl. reflexivity.
Qed.
Theorem map_rev : forall (X Y : Type) (f : X -> Y) (l : list X),
  map f (rev l) = rev (map f l).
Proof.
    intros.
    induction l as [| n l' IHl'].
    - reflexivity.
    - simpl. rewrite <- IHl'. rewrite -> app_map. reflexivity.
Qed.
(* Exercise end *)

(* Exercise: flat_map *)
Fixpoint flat_map {X Y: Type} (f: X -> list Y) (l: list X): list Y :=
    match l with
    | [] => []
    | h :: t => app (f h) (flat_map f t)
    end.
Example test_flat_map1:
  flat_map (fun n => [n;n;n]) [1;5;4]
  = [1; 1; 1; 5; 5; 5; 4; 4; 4].
Proof. 
    reflexivity.
Qed.
(* Exercise end *)

Definition option_map {X Y : Type} (f : X -> Y) (xo : option X)
                      : option Y :=
  match xo with
  | None => None
  | Some x => Some (f x)
  end.

(* Exercise: implicit_args *)
Module ImplicitArgs.
    Fixpoint flat_map (X Y: Type) (f: X -> Y) (l: list X): list Y :=
        match l with
        | [] => []
        | h :: t => app ([f h]) (flat_map X Y f t)
        end.
End ImplicitArgs.
(* Exercise end *)


