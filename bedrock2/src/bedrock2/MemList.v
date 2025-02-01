Require Import coqutil.Map.Interface coqutil.Lift1Prop. Import map.

Section MapListMap.
  Context {key value} {map : map.map key value} {listmap : map.map (key * nat) value}.
  Definition getlevel (n : nat) : listmap -> map :=
    fold (fun leveln (k_i : key * nat) v => let (k, i) := k_i in
                                 if Nat.eqb i n then
                                   put leveln k v else
                                   leveln) empty.
  Definition putlevel (n : nat) : listmap -> map -> listmap :=
    fold (fun lm k v => put lm (k, n) v).
End MapListMap.

Section Sep.
  Context {key value} {map : map (key * nat) value}.
  Definition emp (P : Prop) := fun m : map => m = empty /\ P.
  Definition sep (p q : map -> Prop) m :=
    exists mp mq, split m mp mq /\ p mp /\ q mq.
  Definition ptsto k v := fun m : map => exists n, m = put empty (k, n) v.
  (*what is this*)
  (* Definition read k (P : value -> rep -> Prop) := (ex1 (fun v => sep (ptsto k v) (P v))). *)

  Fixpoint seps (xs : list (rep -> Prop)) : rep -> Prop :=
    match xs with
    | cons x nil => x
    | cons x xs => sep x (seps xs)
    | nil => emp True
    end.
End Sep.

Declare Scope sep_scope.
Delimit Scope sep_scope with sep.
Infix "*" := sep (at level 40, left associativity) : sep_scope.
Infix "⋆" := sep (at level 40, left associativity) : sep_scope.
Notation "m =* P" := ((P%sep) m) (at level 70, only parsing).
Notation "m =*> P" := (exists R, (sep P R) m) (at level 70, only parsing).







































(* Require Import coqutil.Map.Interface coqutil.Lift1Prop. *)
(* Require Import Coq.Lists.List. *)
(* Import ListNotations map. *)

(* Section WithListmap. *)
(*   Context {key value} {map : map key value}. *)
  
(*   Definition disj (m1 m2 : listmap) := forall n k v1 v2, *)
(*     get m1 n k = Some v1 -> get m2 n k = Some v2 -> False. *)
  

(*   (*head of list is zeroth level, etc.  in particular, head1 and head2 are aligned.*) *)
(*   Print putmany. *)
  
(*   Definition  *)

(*   (* Fixpoint putmany_list (len : nat) (m1 m2 : list map) := *) *)
(*   (* match len, m1, m2 with *) *)
(*   (* | S len', a1 :: m1', a2 :: m2' => map.putmany a1 a2 :: putmany_list len' m1' m2' *) *)
(*   (* | S len', [], a2 :: m2' => a2 :: putmany_list len' [] m2' *) *)
(*   (* | S len', a1 :: m1', [] => a1 :: putmany_list len' m1' [] *) *)
(*   (* | S len', [], [] => empty :: putmany_list len' [] [] *) *)
(*   (* | O, _, _ => [] *) *)
(*   (* end. *) Print map.map. *)

(*   Definition split (m m1 m2 : list map) := equiv m (putmany_list m1 m2) /\ disj m1 m2. *)

(*   Definition emp (P : Prop) := fun m => equiv m []. *)
(*   Definition sep (p q : list map -> Prop) m := *)
(*     exists mp mq, split m mp mq /\ p mp /\ q mq. *)
(*   Definition ptsto k v := fun m : list map => exists n, equiv m (repeat map.empty n ++ [map.put empty k v]). *)

(*   (*what is this*) *)
(*   (*Definition read k (P : value -> rep -> Prop) := (ex1 (fun v => sep (ptsto k v) (P v))).*) *)

(*   Fixpoint seps (xs : list (mem -> Prop)) : mem -> Prop := *)
(*     match xs with *)
(*     | cons x nil => x *)
(*     | cons x xs => sep x (seps xs) *)
(*     | nil => emp True *)
(*     end. *)
  
(*   (*Definition mem := nat -> map. *)
(*   Definition equiv (m1 m2 : mem) := forall n, m1 n = m2 n. *)
(*   Definition disj (m1 m2 : mem) := forall n, map.disjoint (m1 n) (m2 n). *)
(*   Definition putmany_tower (m1 m2 : mem) := fun n => map.putmany (m1 n) (m2 n). *)
(*   Definition split (m m1 m2 : mem) := forall n, map.split (m n) (m1 n) (m2 n). *)

(*   Definition emp (P : Prop) := fun m : mem => equiv m (fun _ => map.empty) /\ P. *)
(*   Definition sep (p q : mem -> Prop) m := *)
(*     exists mp mq, split m mp mq /\ p mp /\ q mq. *)
(*   Definition ptsto k v := fun m : mem => exists n, m n = map.put empty k v. *)
(*   (*what is this*) *)
(*   (*Definition read k (P : value -> rep -> Prop) := (ex1 (fun v => sep (ptsto k v) (P v))).*) *)

(*   Fixpoint seps (xs : list (mem -> Prop)) : mem -> Prop := *)
(*     match xs with *)
(*     | cons x nil => x *)
(*     | cons x xs => sep x (seps xs) *)
(*     | nil => emp True *)
(*     end.*) *)

  
(* End Sep. *)

(* (*Declare Scope sep_scope. *)
(* Delimit Scope sep_scope with sep. *)
(* Infix "*" := sep (at level 40, left associativity) : sep_scope. *)
(* Infix "⋆" := sep (at level 40, left associativity) : sep_scope. *)
(* Notation "m =* P" := ((P%sep) m) (at level 70, only parsing). *)
(* Notation "m =*> P" := (exists R, (sep P R) m) (at level 70, only parsing).*) *)
