From LECTURES Require Export W2.

Module NatList.

(** Lists in Rocq *)

Inductive natlist : Type :=
  | nil
  | cons (n : nat) (l : natlist).

Definition mylist := cons 1 (cons 2 (cons 3 nil)).

Compute mylist.

Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Definition mylist1 := 1 :: (2 :: (3 :: nil)).
Definition mylist2 := 1 :: 2 :: 3 :: nil.
Definition mylist3 := [1;2;3].

Compute mylist1.
Compute mylist2.

(** Next let's look at several functions for constructing and
    manipulating lists.  First, the [repeat] function, which takes a
    number [n] and a [count] and returns a list of length [count] in
    which every element is [n]. *)

Fixpoint repeat (n count : nat) : natlist :=
  match count with
  | O => nil
  | S count' => n :: (repeat n count')
  end.
  
(** The [length] function calculates the length of a list. *)

Fixpoint length (l:natlist) : nat :=
  match l with
  | nil => O
  | h :: t => S (length t)
  end.
  
Definition hd (default : nat) (l : natlist) : nat :=
  match l with
  | nil => default
  | h :: t => h
  end.

Definition tl (l : natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => t
  end.

(* ----------------------------------------------------------------- *)
(** *** Append *)

(** The [app] function appends (concatenates) two lists. *)

Fixpoint app (l1 l2 : natlist) : natlist :=
  match l1 with
  | nil    => l2
  | h :: t => h :: (app t l2)
  end.

(** Since [app] will be used extensively, it is again convenient
    to have an infix operator for it. *)

Notation "x ++ y" := (app x y)
                     (right associativity, at level 60).

Compute ([1;2;3] ++ [4;5]).

(** * Reasoning About Lists *)

(** As with numbers, simple facts about list-processing
    functions can sometimes be proved entirely by simplification. *)

Theorem nil_app : forall l : natlist,
  [] ++ l = l.
Proof. reflexivity. Qed.


(** Also, as with numbers, it is sometimes helpful to perform case
    analysis on the possible shapes (empty or non-empty) of an unknown
    list. *)

Theorem tl_length_pred : forall l:natlist,
  pred (length l) = length (tl l).
Proof.
  intros l. destruct l as [| n l'].
  - (* l = nil *)
    reflexivity.
  - (* l = cons n l' *)
    reflexivity.  Qed.
    
Theorem app_assoc : forall l1 l2 l3 : natlist,
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  intros l1 l2 l3. induction l1 as [| n1 l1'].
  - reflexivity.
  - simpl. rewrite IHl1'. reflexivity.
Qed.

Theorem repeat_double_firsttry : forall c n: nat,
  repeat n c ++ repeat n c = repeat n (c + c).
Proof. intros c n. induction c as [| c' IHc'].
- reflexivity.
- simpl. Abort.

Theorem repeat_plus : forall c1 c2 n: nat,
  repeat n c1 ++ repeat n c2 = repeat n (c1 + c2).
Proof. intros c1 c2 n. induction c1 as [| c1' IHc1'].
- reflexivity.
- simpl. rewrite IHc1'. reflexivity.
Qed.

Fixpoint rev (l: natlist) :=
match l with
| [] => []
| hd :: tl => rev tl ++ [hd]
end.

Theorem rev_length_first_try : forall (l: natlist),
  length (rev l) = length l.
Proof. intros l. induction l as [|n l' IHl'].
- reflexivity.
- simpl. rewrite <- IHl'. Abort.

Theorem length_append_1 : forall (l: natlist) (n:nat),
  length(l ++ [n]) = S(length l).
Proof. intros l n. induction l as [| m l' IHl'].
- reflexivity.
- simpl. rewrite IHl'. reflexivity.
Qed.

Theorem rev_length :  forall (l: natlist),
  length (rev l) = length l.
Proof. intros l. induction l as [|n l' IHl'].
- reflexivity.
- simpl. rewrite <- IHl'. rewrite length_append_1. reflexivity.
Qed.

Theorem length_append : forall (l1 l2: natlist),
  length(l1 ++ l2) = length l1 + length l2.
Proof. intros l1 l2. induction l1 as [| n l1' IHl1'].
- reflexivity.
- simpl. rewrite IHl1'. reflexivity.
Qed.

End NatList.

(** Polymorphism in Rocq
-Instead of defining separate types for list of bools, list of days,
list of bins, list of lists, etc., we can define a generic list type
 *)
 
Inductive list (X:Type) : Type :=
| nil
| cons (x : X) (l : list X).

Check list.

Check nil.

Check nil nat.

(**
- The X parameter to the list type automatically becomes a parameter for
the constructors.
*)

Check cons nat 5 (nil nat).

Fixpoint repeat (X: Type) (n : X) (count : nat) : list X :=
  match count with
  | O => nil X
  | S count' => cons X n (repeat X n count')
  end.
  
Compute (repeat nat 2 4).

Compute (repeat bool true 2).

Module MumbleGrumble.

Inductive mumble : Type :=
  | a
  | b (x : mumble) (y : nat)
  | c.

Inductive grumble (X:Type) : Type :=
  | d (m : mumble)
  | e (x : X).

(** Which of the following are well-typed elements of [grumble X] for
    some type [X]?  (Add YES or NO to each line.)
      - [d (b a 5)]
      - [d mumble (b a 5)]
      - [d bool (b a 5)]
      - [e bool true]
      - [e mumble (b c 0)]
      - [e bool (b c 0)]
      - [c]  *)
(* FILL IN HERE *)
End MumbleGrumble.

(** Type inference in Rocq *)

Fixpoint repeat' X x count :=
  match count with
  | 0 => nil X
  | S count' => cons X x (repeat' X x count')
  end.
  
Check repeat'.

(** We can also make the type arguments to constructors
and functions implicit: *)

Arguments nil {X}.
Arguments cons {X}.
Arguments repeat {X}.

Check cons 5 nil.
Check cons false (cons true nil).

Compute (repeat 2 4).

Fixpoint repeat'' {X : Type} x count : list X :=
  match count with
  | 0        => nil
  | S count' => cons x (repeat'' x count')
  end.
  
Compute (repeat 2 4).
  
Fixpoint app {X : Type} (l1 l2 : list X) : list X :=
  match l1 with
  | nil      => l2
  | cons h t => cons h (app t l2)
  end.

Fail Definition mynil := nil.


Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                     (at level 60, right associativity).
                     
Inductive prod (X Y: Type) :=
| pair (x : X) (y : Y).

Arguments pair {X} {Y}.

Definition a_prod := pair 5 true.

Compute a_prod.

Inductive option (X : Type) :=
| Some (x : X)
| None.

Arguments Some {X}.

Compute (Some 5).


(**
Higher-order programming in Rocq

- Functions in Rocq are first-class citizens, and hence can be passed
as arguments to other functions, returned as results, stored in data
structures, etc.
*)

Fixpoint filter {X:Type} (test: X -> bool) (l : list X) :=
  match l with
  | [] => []
  | h :: t => if test h then h :: (filter test t)
              else filter test t
  end.

Compute (filter even [1;2;3;4]).

(** Compute (filter (fun l => (length l) =? 1) [ [1;2]; [2]; [3;4] ]).*)








