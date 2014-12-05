(* Utilities to do functional programming in Coq *)

Set Implicit Arguments.

Require Import String.
Local Open Scope string_scope.
Require Import List.
Import ListNotations.
Local Open Scope list_scope.

(* functional programming utilities *)

Require Import Program.Basics.

Infix "<<" := compose (at level 40) : prog_scope.
Infix ">>" := (flip compose) (at level 40) : prog_scope.

Definition apply {A B} (f : A -> B) x := f x.
Infix "$" := apply (at level 85, right associativity) : prog_scope.

Definition flip A B C (f : A -> B -> C) b a := f a b.

Local Open Scope prog_scope.

(* option utilities *)

Fixpoint msum {A} (ls : list (option A)) : option A :=
  match ls with
    | Some a :: _ => Some a
    | None :: ls => msum ls
    | nil => None
  end.

Definition default A def (o : option A) : A :=
  match o with
    | Some a => a
    | None => def
  end.

Require Import Ascii.
Require Import Bool.
Local Open Scope bool_scope.
Require Import NArith.
Local Open Scope N_scope.
Local Open Scope nat_scope.

(* list utilities *)

Definition flat {A} (ls : list (list A)) := flat_map id ls.

Definition sum A (zero : A) (add : A -> A -> A) (ls : list A) : A := fold_left add ls zero.

Fixpoint repeat A (a : A) n :=
  match n with
    | 0 => nil
    | S n => a :: repeat a n
  end.

Definition lcshift A n (ls : list A) := skipn n ls ++ firstn n ls.

Definition rcshift A n (ls : list A) := lcshift (length ls - n) ls.

Fixpoint prependToAll A (sep : A) ls :=
  match ls with
    | nil => nil
    | x :: xs => sep :: x :: prependToAll sep xs
  end.

Definition intersperse A (sep : A) ls :=
  match ls with
    | nil => nil
    | x :: xs => x :: prependToAll sep xs
  end.

Definition range A begin len (ls : list A) := firstn len (skipn begin ls).

Fixpoint forall2 A B (p : A -> B -> bool) ls1 ls2 :=
  match ls1, ls2 with
    | a :: ls1, b :: ls2 => p a b && forall2 p ls1 ls2
    | nil, nil => true
    | _, _ => false
  end.

Fixpoint map2 A B C (f : A -> B -> C) ls1 ls2 :=
  match ls1, ls2 with
    | a :: ls1, b :: ls2 => f a b :: map2 f ls1 ls2
    | _, _ => nil
  end.

Fixpoint mapi' base {A B} (f : nat -> A -> B) (ls : list A) : list B :=
  match ls with
    | x :: xs => f base x :: mapi' (S base) f xs
    | nil => nil
  end.

Definition mapi {A B} := @mapi' 0 A B.

(* a specialize version of fold_left for [begin,begin+1,...,begin+len-1] *)
Fixpoint iter_range A (f : A -> nat -> A) begin len init :=
  match len with
    | 0 => init
    | S n' => iter_range f (S begin) n' (f init begin)
  end.

Definition iter A f := @iter_range A f 0.

(* f (...) (begin+len-1) :: ... :: f (f init begin) (begin+1) :: f init begin :: init_res *)
Definition iter_range_collect_rev A (f : A -> nat -> A) begin len init init_res: list A :=
  snd (iter_range 
         (fun p n => 
            let old := fst p in 
            let ls := snd p in 
            let new := f old n in
            (new, new :: ls))
         begin len (init, init_res)).

Definition iter_range_collect A f begin len (init : A) init_res := rev (iter_range_collect_rev f begin len init (rev init_res)).

Definition iter_collect A f n := @iter_range_collect A f 0 n .

(* a special version of map for [begin; begin+1; ...; begin+len-1] *)
Fixpoint for_range A begin len (f : nat -> A) :=
  match len with
    | 0 => []
    | S n => f begin :: for_range (S begin) n f
  end.

Definition for_n A len := @for_range A 0 len.

(* slicing *)
Fixpoint slice' (count : nat) A (width : nat) (ls : list A) : list (list A) :=
  match count with
    | 0 => nil
    | S count => firstn width ls :: slice' count width (skipn width ls)
  end.

Require Import NPeano.

Definition slice A (width : nat) (ls : list A) : list (list A) :=
  let n := length ls / width in 
  let res := slice' n width ls in
  let len := width * n in
  match length ls - len with
    | 0 => res
    | _ => res ++ [skipn len ls]
  end.

Definition mapi_every A (width : nat) (f : nat -> list A -> list A) (ls : list A) : list A :=
  flat (mapi f (slice width ls)).

Definition map_every A n f := @mapi_every A n (fun _ e => f e).

(* string/ascii utilities *)

(* if ch in in range [a, b], return (Some (ch - a + base)) *)
Definition N_of_ascii_in (a b : ascii) (base : N) (ch: ascii) : option N :=
  (let asc := N_of_ascii ch in
   let ascA := N_of_ascii a in
   let ascB := N_of_ascii b in
   if (ascA <=? asc) && (asc <=? ascB) then
     Some (asc - ascA + base)
   else
     None
  )%N.

Fixpoint str_to_list (str : string) :=
  match str with
    | String c s => c :: str_to_list s
    | _ => nil
  end.

Fixpoint list_to_str ls : string :=
  match ls with
    | c :: ls => String c (list_to_str ls)
    | nil => EmptyString
  end.

Definition intersperse_every n sep := str_to_list >> slice n >> intersperse (str_to_list sep) >> flat >> list_to_str.

Definition sep := intersperse_every.

(* tactics *)

Ltac r := vm_compute; reflexivity.

