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


