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

(* Fold *)
Fixpoint fold {X Y: Type} (f : X->Y->Y) (l : list X) (b : Y)
                         : Y :=
  match l with
  | nil => b
  | h :: t => f h (fold f t b)
  end.

  Check (fold andb) : list bool -> bool -> bool.
Example fold_example1 :
  fold andb [true;true;false;true] true = false.
Proof. reflexivity. Qed.

Example fold_example2 :
  fold mult [1;2;3;4] 1 = 24.
Proof. reflexivity. Qed.

Example fold_example3 :
  fold app [[1];[];[2;3];[4]] [] = [1;2;3;4].
Proof. reflexivity. Qed.

(* Exercise: fold_types_different *)
(* Check fold (fun x y => x <=? y) [1;2;3;4] 0 = 10. *)
(* Exercise end *)

(* Functions That construct functions *)
Definition constfun {X: Type} (x: X) : nat -> X :=
  fun (k:nat) => x.
Definition ftrue := constfun true.
Example constfun_example1 : ftrue 0 = true.
Proof. reflexivity. Qed.

Example constfun_example2 : (constfun 5) 99 = 5.
Proof. reflexivity. Qed.

(* This operator is right-associative, 
so the type of plus is really a shorthand for nat -> (nat -> nat) *)
Check plus : nat -> nat -> nat.
Definition plus3 := plus 3.
Check plus3 : nat -> nat.
Example test_plus3 : plus3 4 = 7.
Proof. reflexivity. Qed.
Example test_plus3' : doit3times plus3 0 = 9.
Proof. reflexivity. Qed.
Example test_plus3'' : doit3times (plus 3) 0 = 9.
Proof. reflexivity. Qed.

(* Additional Exercises *)

Module Exercises.
(* Exercise: fold_length *)
Definition fold_length {X : Type} (l : list X) : nat :=
  fold (fun _ n => S n) l 0.
Example test_fold_length1 : fold_length [4;7;0] = 3.
Proof. reflexivity. Qed.

Theorem fold_length_correct : forall X (l : list X),
  fold_length l = length l.
Proof.
    intros.
    induction l.
    - reflexivity.
    - simpl. rewrite <- IHl. reflexivity.
Qed.
(* Exercise end *)

(* Exercise: fold_map *)

Definition fold_map {X Y: Type} (f: X -> Y) (l: list X): list Y :=
    fold (fun x t => (f x) :: t) l [].

Example test_fold_map1: fold_map (fun x => x + 1) [1;2;3] = [2;3;4].
Proof. reflexivity. Qed.

Definition manual_grade_for_fold_map : option (nat*string) := None.

Theorem fold_map_correct : forall X Y (f: X -> Y) (l: list X),
  fold_map f l = map f l.
Proof.
    intros.
    induction l.
    - reflexivity.
    - simpl. rewrite <- IHl. reflexivity.
Qed.
(* Exercise end *)

(* Exercise: currying *)
Definition prod_curry {X Y Z : Type}
  (f : X * Y -> Z) (x : X) (y : Y) : Z := f (x, y).

Definition prod_uncurry {X Y Z : Type}
    (f : X -> Y -> Z) (p : X * Y) : Z := f (fst p) (snd p).

Example test_map1': map (plus 3) [2;0;2] = [5;3;5].
Proof. reflexivity. Qed.

Check @prod_curry.
Check @prod_uncurry.
Theorem uncurry_curry : forall (X Y Z : Type)
                        (f : X -> Y -> Z)
                        x y,
  prod_curry (prod_uncurry f) x y = f x y.
Proof.
    intros.
    reflexivity.
Qed.

Theorem curry_uncurry : forall (X Y Z : Type)
                        (f : (X * Y) -> Z)
                        p,
  prod_uncurry (prod_curry f) p = f p.
Proof.
    intros.
    destruct p.
    - reflexivity.
Qed.


(* Exercise: nth_error_informal *)
(* 
Theorem: For any X, l, and n,
      nth_error l n = Some x
    if and only if
      x is the nth element of l. 
Proof:
    Suppose we have a list l of type X and a natural number n.
    We will prove the theorem by induction on l.
    - First, suppose l = [].
        - We must show that nth_error [] n = Some x if and only if x is the nth element of [].
        - By the definition of nth_error, nth_error [] n = None for any n.
        - Since there are no elements in [], x cannot be the nth element of [].
        - Therefore, the theorem holds in this case.
    - Next, suppose l = h :: t for some h of type X and t of type list X.
        - We must show that nth_error (h :: t) n = Some x if and only if x is the nth element of h :: t.
        - By the definition of nth_error, if n = 0, then nth_error (h :: t) n = Some h.
        - If x is the nth element of h :: t, then x = h.
        - If n = 0, then x = h is the nth element of h :: t.
        - If n > 0, then x is the nth element of t.
        - By the induction hypothesis, nth_error t (n - 1) = Some x if and only if x is the (n - 1)th element of t.
        - Therefore, the theorem holds in this case.
    - By induction, the theorem holds for all lists l and natural numbers n.
*)
Definition manual_grade_for_informal_proof : option (nat*string) := None.
(* Exercise end *)

(* Church Numerals *)

Module Church.
Definition cnat := forall X : Type, (X -> X) -> X -> X.

Definition one : cnat :=
  fun (X : Type) (f : X -> X) (x : X) => f x.

Definition two : cnat :=
  fun (X : Type) (f : X -> X) (x : X) => f (f x).

Definition zero : cnat :=
  fun (X : Type) (f : X -> X) (x : X) => x.

Definition three : cnat := @doit3times.

Definition zero' : cnat :=
  fun (X : Type) (succ : X -> X) (zero : X) => zero.
Definition one' : cnat :=
  fun (X : Type) (succ : X -> X) (zero : X) => succ zero.
Definition two' : cnat :=
  fun (X : Type) (succ : X -> X) (zero : X) => succ (succ zero).

Example zero_church_peano : zero nat S O = 0.
Proof. reflexivity. Qed.
Example one_church_peano : one nat S O = 1.
Proof. reflexivity. Qed.
Example two_church_peano : two nat S O = 2.
Proof. reflexivity. Qed.


(* Exercise: church_scc *)

Definition scc (n : cnat) : cnat :=
  fun (X : Type) (f : X -> X) (x : X) => f (n X f x).

Example scc_1 : scc zero = one.
Proof. reflexivity. Qed.
Example scc_2 : scc one = two.
Proof. reflexivity. Qed.
Example scc_3 : scc two = three.
Proof. reflexivity. Qed.

(* Exercise end *)


(* Exercise: church_plus *)
Definition plus (n m : cnat) : cnat :=
  fun (X : Type) (f : X -> X) (x : X) => n X f (m X f x).
Example plus_1 : plus zero one = one.
Proof. reflexivity. Qed.
Example plus_2 : plus two three = plus three two.
Proof. reflexivity. Qed.
Example plus_3 :
  plus (plus two two) three = plus one (plus three three).
Proof. reflexivity. Qed.

(* Exercise end *)

(* Exercise: church_mult *)
Definition mult (n m : cnat) : cnat
    := fun (X : Type) (f : X -> X) (x : X) => n X (m X f) x.
Example mult_1 : mult one one = one.
Proof. reflexivity. Qed.
Example mult_2 : mult zero (plus three three) = zero.
Proof. reflexivity. Qed.
Example mult_3 : mult two three = plus three three.
Proof. reflexivity. Qed.
(* Exercise end *)

(* Exercise: church_exp *)
Definition exp (n m : cnat) : cnat
    := fun (X : Type) (f : X -> X) (x : X) => (m (X -> X) (n X) f) x.

Example exp_1 : exp two two = plus two two.
Proof. reflexivity. Qed.
Example exp_2 : exp three zero = one.
Proof. reflexivity. Qed.
Example exp_3 : exp three two = plus (mult two (mult two two)) one.
Proof. reflexivity. Qed.
(* Exercise end *)

End Church.

End Exercises.




