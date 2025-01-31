Require Import coqutil.Map.Interface coqutil.Lift1Prop.
Require Import Coq.Lists.List.
Import ListNotations map.

Section Sep.
  Context {key value} {map : map key value}.

  (*Inductive disj_same_length : list map -> list map -> Prop :=
  | disj_nil : disj_same_length [] []
  | disj_cons a1 a2 m1 m2 : map.disjoint a1 a2 ->
                            disj_same_length m1 m2 ->
                            disj_same_length (a1 :: m1) (a2 :: m2).

  Definition disj_length_leq (m1 m2 : list map) :=
    (exists m0 m1', m1 = m0 ++ m1' /\ disj_same_length m1' m2).

  (*this is obnoxious*)
  Definition disj (m1 m2 : list map) :=
    disj_length_leq m1 m2 \/ disj_length_leq m2 m1.

  Definition putmany_list (m1 m2 : list map) :=
    match m1, m2 with
    | a1 :: m1', a2 :: m2' => map.putmany a1 a2 :: putmany_list m1' (*agh no they need to be reversed*)*)

  Definition mem := nat -> map.
  Definition equiv (m1 m2 : mem) := forall n, m1 n = m2 n.
  Definition disj (m1 m2 : mem) := forall n, map.disjoint (m1 n) (m2 n).
  Definition putmany_tower (m1 m2 : mem) := fun n => map.putmany (m1 n) (m2 n).
  Definition split (m m1 m2 : mem) := forall n, map.split (m n) (m1 n) (m2 n).

  Definition emp (P : Prop) := fun m : mem => equiv m (fun _ => map.empty) /\ P.
  Definition sep (p q : mem -> Prop) m :=
    exists mp mq, split m mp mq /\ p mp /\ q mq.
  Definition ptsto k v := fun m : mem => exists n, m n = map.put empty k v.
  (*what is this*)
  (*Definition read k (P : value -> rep -> Prop) := (ex1 (fun v => sep (ptsto k v) (P v))).*)

  Fixpoint seps (xs : list (mem -> Prop)) : mem -> Prop :=
    match xs with
    | cons x nil => x
    | cons x xs => sep x (seps xs)
    | nil => emp True
    end.
End Sep.

(*Declare Scope sep_scope.
Delimit Scope sep_scope with sep.
Infix "*" := sep (at level 40, left associativity) : sep_scope.
Infix "⋆" := sep (at level 40, left associativity) : sep_scope.
Notation "m =* P" := ((P%sep) m) (at level 70, only parsing).
Notation "m =*> P" := (exists R, (sep P R) m) (at level 70, only parsing).*)
