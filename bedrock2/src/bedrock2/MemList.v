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
  Context {addrs levels : Type}.
  Definition emp (P : Prop) := fun m : map => m = empty /\ P.
  Definition sep (p q : map -> Prop) m :=
    exists mp mq, split m mp mq /\ p mp /\ q mq.
  Definition ptsto k v := fun (H : addrs * levels -> Prop) (m : addrs * levels -> map) =>
                            exists n, forall a ls,
                              H (a, ls) ->
                              m (a, ls) = put empty (k, n ls) v.
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


Require Import BinIntDef coqutil.Word.Interface coqutil.Word.Bitwidth coqutil.Word.LittleEndianList.
Require Import bedrock2.Syntax.
Print LittleEndianList.le_combine.
Print LittleEndianList.le_split.
Search access_size.access_size.
Require Import Coq.ZArith.ZArith.

Section WithParameters.
  Context {width: Z}{BW: Bitwidth width}{word: word.word width}{listmem: map.map (word * nat) Byte.byte}.

Definition wordnat_eqb : word * nat -> word * nat -> bool. Admitted.

Global Instance wordnat_eqb_spec :
  word.ok word -> forall a b : word*nat, BoolSpec (a = b) (a <> b) (wordnat_eqb a b). Admitted.

(*Lemma load_one_of_sep (addr : word) (value : Init.Byte.byte) (R : listmem -> Prop) (m : listmem) :
    m =* ptsto addr value * R ->
    Memory.load access_size.one m addr = Some (word.of_Z (Byte.byte.unsigned value)).*)

  Open Scope Z_scope.

  Definition bytes_per_word(width: Z): Z := (width + 7) / 8.

  Definition bytes_per sz :=
    match sz with
      | access_size.one => 1 | access_size.two => 2 | access_size.four => 4
      | access_size.word => Z.to_nat (bytes_per_word width)
    end%nat. Print LittleEndianList.le_split.

  Definition to_bytes (w : word) (sz : access_size) : list Byte.byte :=
    LittleEndianList.le_split (bytes_per sz) (word.unsigned w).

  Definition of_bytes (l : list Byte.byte) : word :=
    word.of_Z (LittleEndianList.le_combine l).
  
  Fixpoint array_byte (start : word) (xs : list Byte.byte) :=
    match xs with
    | nil => emp True
    | cons x xs => sep (ptsto start x) (array_byte (word.add start (word.of_Z 1)) xs)
    end.

  Definition anybytes' a n m : Prop :=
    exists l, length l = n /\ array_byte a l m.
End WithParameters.





































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
