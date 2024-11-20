Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List. Import ListNotations.
Require Import bedrock2.MetricLogging.
Require Import bedrock2.MetricCosts.
Require Import coqutil.Macros.unique.
Require Import bedrock2.Memory.
Require Import compiler.util.Common.
Require Import coqutil.Decidable.
Require Import coqutil.Datatypes.PropSet.
Require Import coqutil.Byte.
Require Import bedrock2.Syntax.
Require Import coqutil.Z.Lia.
Require Import coqutil.Tactics.Simp.
Require Import bedrock2.Semantics.
Require Import coqutil.Datatypes.ListSet.
Require Import coqutil.Map.OfListWord.
Require Import coqutil.Word.Bitwidth.
Require Import coqutil.Word.Interface.
Local Hint Mode Word.Interface.word - : typeclass_instances.
Require Import compiler.FlatImp.
Print stmt.

Require Import coqutil.Map.SortedList.
Require Import coqutil.Map.SortedListZ.
Import SortedList.parameters.
(*
  Definition env: map.map String.string Syntax.func := SortedListString.map _.
#[export] Instance env_ok: map.ok env := SortedListString.ok _.
 *)

Section RHS.
  Context {varname : Type}.
  Definition as_to_Z (x : access_size) :=
    match x with
    | access_size.one => 0
    | access_size.two => 1
    | access_size.four => 2
    | access_size.word => 3
    end.

  Check SOp.
  Inductive rhs_op :=
  | RLoad | RStore | RInlinetable | RLit | ROp | RSet.

  Definition rhs : Type := rhs_op * option access_size * option varname (*rs1*) * option Z (*imm*) * option (list byte) * option bopname * option (@operand varname).

  Definition rhs_of_stmt (s : stmt varname) : rhs :=
    match s with
    | SLoad sz x a offset => (RLoad, Some sz, Some a, Some offset, None, None, None)
    | SStore sz x a offset => (RStore, Some sz, Some a, Some offset, None, None, None)
    | SInlinetable sz x t i => (RInlinetable, Some sz, Some i, None, Some t, None, None)
    | SLit x v => (RLit, None, None, Some v, None, None, None)
    | SOp x op y z => (ROp, None, Some y, None, None, Some op, Some z)
    | SSet x y => (RSet, None, Some y, None, None, None, None)
    | _ => (RSet, None, None, None, None, None, None)
    end.

  Definition rhstype_to_Z (x : rhs_op) : Z :=
    match x with
    | RLoad => 0
    | RStore => 1
    | RInlinetable => 2
    | RLit => 3
    | ROp => 4
    | RSet => 5
    end.

  Definition bopname_to_Z (x : bopname) : Z :=
    match x with
    | bopname.add => 0
    | bopname.sub => 1
    | bopname.mul => 2
    | bopname.mulhuu => 3
    | bopname.divu => 4
    | bopname.remu => 5
    | bopname.and => 6
    | bopname.or => 7
    | bopname.xor => 8
    | bopname.sru => 9
    | bopname.slu => 10
    | bopname.srs => 11
    | bopname.lts => 12
    | bopname.ltu => 13
    | bopname.eq => 14
    end.

  Print operand.
  Context (lt_varname : varname -> varname -> bool).
  Context (lt_varname_strict : strict_order lt_varname).
  
  Definition operand_to_tuple (x : (@operand varname)) :=
    match x with
    | Var x => (0, Some x, None)
    | Const y => (1, None, Some y)
    end.
  
  Check (lexicog4 (lexicog4 (lift2 rhstype_to_Z Z.ltb) (with_bot (lift2 as_to_Z Z.ltb)) (with_bot lt_varname) (with_bot Z.ltb)) (with_bot (lexicog (lift2 byte.unsigned Z.ltb))) (with_bot (lift2 bopname_to_Z Z.ltb)) (with_bot (lift2 operand_to_tuple (lexicog3 Z.ltb (with_bot lt_varname) (with_bot Z.ltb))))).

  (*I suspect I should be able to make coq do this, given with_bot, lift2, Z.lt, etc.*)
  Definition rhslt : rhs -> rhs -> bool :=
    lexicog4 (lexicog4 (lift2 rhstype_to_Z Z.ltb) (with_bot (lift2 as_to_Z Z.ltb)) (with_bot lt_varname) (with_bot Z.ltb)) (with_bot (lexicog (lift2 byte.unsigned Z.ltb))) (with_bot (lift2 bopname_to_Z Z.ltb)) (with_bot (lift2 operand_to_tuple (lexicog3 Z.ltb (with_bot lt_varname) (with_bot Z.ltb)))).

  Lemma rhslt_strict : strict_order rhslt.
  Proof. Check Z_strict_order.
    repeat (apply lexicog_strict || apply lt_varname_strict || apply lexicog4_strict || apply lexicog3_strict || apply Z_strict_order || apply with_bot_strict || match goal with | |- strict_order (lift2 _ _) => apply lift2_strict end).
    - intros. destruct x, y; simpl in H; reflexivity || congruence.
    - intros. destruct x, y; simpl in H; reflexivity || congruence.
    - exact byte.unsigned_inj.
    - intros. destruct x, y; simpl in H; reflexivity || congruence.
    - intros. destruct x, y; simpl in H; reflexivity || congruence.
  Qed.
End RHS.
  
Section VarName.
  Context (varname : Type).
  Context (varname_lt : varname -> varname -> bool).
  Context (varname_lt_strict : strict_order varname_lt).

  Definition label_lt := lexicog2 varname_lt (lift2 Z.of_nat Z.ltb).

  Lemma label_lt_strict : strict_order label_lt.
  Proof. 
    apply lexicog2_strict.
    1: apply varname_lt_strict. apply lift2_strict. 1: apply Z_strict_order.
    Search (forall x y : nat, Z.of_nat x = Z.of_nat y -> x = y). exact Nat2Z.inj.
  Qed.
    
  Definition rhs_to_label_parameters : parameters :=
    {| key := rhs;
      ltb := rhslt label_lt;
      value := varname * nat|}.

  Definition rhslabel_strict :
    strict_order rhs_to_label_parameters.(ltb).
  Proof.
    apply rhslt_strict. apply label_lt_strict.
  Defined.

  Check (SortedList.map rhs_to_label_parameters rhslabel_strict).

  Definition rhs_to_label := SortedList.map rhs_to_label_parameters rhslabel_strict.

  Definition label_to_label_parameters : parameters :=
    {| key := varname * nat;
      value := varname * nat;
      ltb := label_lt |}.

  Definition label_to_label := SortedList.map label_to_label_parameters label_lt_strict.

  Definition label_to_stmt_parameters : parameters :=
    {| key := varname * nat;
      value := stmt (varname * nat);
      ltb := label_lt |}.

  Definition label_to_stmt := SortedList.map label_to_stmt_parameters label_lt_strict.

  Definition varname_to_nat_parameters : parameters :=
    {| key := varname;
      value := nat;
      ltb := varname_lt |}.

  Definition varname_to_nat := SortedList.map varname_to_nat_parameters varname_lt_strict.
  
  
  (*
      Inductive stmt: Type :=
    | SLoad(sz: Syntax.access_size)(x: varname)(a: varname)(offset: Z)
    | SStore(sz: Syntax.access_size)(a: varname)(v: varname)(offset: Z)
    | SInlinetable(sz: Syntax.access_size)(x: varname)(t: list Byte.byte)(i: varname)
    | SStackalloc(x : varname)(nbytes: Z)(body: stmt)
    | SLit(x: varname)(v: Z)
    | SOp(x: varname)(op: bopname)(y: varname)(z: operand)
    | SSet(x y: varname)
    | SIf(cond: bcond)(bThen bElse: stmt)
    | SLoop(body1: stmt)(cond: bcond)(body2: stmt)
    | SSeq(s1 s2: stmt)
    | SSkip
    | SCall(binds: list varname)(f: String.string)(args: list varname)
    | SInteract(binds: list varname)(a: String.string)(args: list varname).

   *)
  Existing Instance varname_to_nat.
  Definition get := @map.get _ _ varname_to_nat.
  Definition getnat (count : map.rep) (x : varname) :=
    match get count x with
    | Some n => n
    | None => O
    end.
  Definition inc (count : map.rep) (x : varname) :=
    map.put count x (S (getnat count x)).
  Print operand.
  Definition label_operand (x : @operand varname) (count : map.rep) :
    @operand (varname * nat) :=
    match x with
    | Var x => Var (x, getnat count x)
    | Const x => Const x
    end.
                     
  Fixpoint ssa' (count : map.rep) (s : stmt varname) :
    stmt (varname * nat) * varname_to_nat :=
    match s with
    | SLoad sz x a offset =>
        (SLoad sz (x, S (getnat count x)) (a, getnat count a) offset, inc count x)
    | SStore sz x a offset =>
        (SStore sz (x, getnat count x) (a, getnat count a) offset, count)
    | SInlinetable sz x t i =>
        (SInlinetable sz (x, S (getnat count x)) t (i, getnat count i), inc count x)
    | SStackalloc x nbytes body => (SSkip, map.empty)
    | SLit x v =>
        (SLit (x, S (getnat count x)) v, inc count x)
    | SOp x op y z =>
        (SOp (x, S (getnat count x)) op (y, getnat count y) (label_operand z count), inc count x)
    | SSet x y =>
        (SSet (x, S (getnat count x)) (y, getnat count y), inc count x)
    | SIf cond bThen bElse => (SSkip, map.empty)
    | SLoop body1 cond body2 => (SSkip, map.empty)
    | SSeq s1 s2 =>
        let (s1', count') := ssa' count s1 in
        let (s2', count'') := ssa' count' s2 in
        (SSeq s1' s2', count'')
    | SSkip => (SSkip, count)
    | SCall binds f args => (SSkip, map.empty)
    | SInteract binds a args => (SSkip, map.empty)
    end.

  Definition ssa := ssa' map.empty.

  
  (*when we get to *)
  Definition get_default {A B : Type} {mt} m x d :=
    match @map.get A B mt m x with
    | Some y => y
    | None => d
    end.
  Print SortedList.map.

  Print parameters.Build_parameters.
  Print parameters. Check rhslt. Check lexicog2.

  
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word byte}.
  
  (*Note: I treat names as if it is magical in certain ways.
    The domain is actually statements mod some equivalence relation, wheere for example:
    - SLit "1" 1 = SLit "2" 1
    - "z" := "x" + "y" = "ry" = "y" + "x"
    That is, two operations are the same if they're the same.
    I should actually implement this rather than just pretending that it works.
   *)
  Fixpoint lvn' (names : rhs_to_label) (values : label_to_stmt)
    (aliases : label_to_label) (s : stmt (varname * nat)) :=
    match s with
    | SLoad sz x a offset =>
        (*first, get canonical names of variables appearing in the line*)
        let a := get_default aliases a a in
        (*then, simplify if possible.*)
        (*nothing to do here, since it's a load.*)

        (*then, check if we've seen this before*)
        (*oops, actually can't do this since it's a load, and memory might've changed.*)
        (*I could and maybe should do something cleverer for loads and stores.*)
        (SLoad sz x a offset, names, values, aliases)
    | SStore sz x a offset =>
        let a := get_default aliases a a in
        (SStore sz x a offset, names, values, aliases)
    | SInlinetable sz x t i =>
        (*canonical names*)
        let i := get_default aliases i i in
        (*simplify*)
        let simplified :=
          match map.get values i with
          | Some (SLit _ c) =>
              let val := 0 (*should actually evaluate the thing*) in SLit x val
          | _ => SInlinetable sz x t i
          end in
        (*check if we've seen this before:
          - if so, update aliases appropriately, and skip
          - otherwise, add to list of names, and don't skip *)
        match map.get names (rhs_of_stmt simplified) with
        | None => (simplified, map.put names (rhs_of_stmt simplified) x, map.put values x simplified, aliases)
        | Some x' => (SSkip, names, values, map.put aliases x x')
        end
    | SStackalloc x nbytes body => (SSkip, map.empty, map.empty, map.empty)
    | SLit x v =>
        match map.get names (rhs_of_stmt (SLit x v)) with
        | None => (SLit x v, map.put names (rhs_of_stmt (SLit x v)) x, map.put values x (SLit x v), aliases)
        | Some x' => (SSkip, names, values, map.put aliases x x')
        end
    | SOp x op y z =>
        let y := get_default aliases y y in
        let z := match z with
                 | Var z => Var (get_default aliases z z)
                 | Const z => Const z
                 end in
        (*this would be the place to put multiply-by-zero stuff and so on.
          for now it's just simple constant folding.*)
        let simplified :=
          match map.get values y with
          | Some (SLit _ c1) =>
              match z with
              | Const c2 => SLit x (word.unsigned (interp_binop op (word.of_Z c1) (word.of_Z c2)))(*TODO: wouldn't have to deal with word-to-nat conversions if i would add a word literal construct*)
              | Var z =>
                  match map.get values z with
                  | Some (SLit _ c2) => SLit x (word.unsigned (interp_binop op (word.of_Z c1) (word.of_Z c2)))
                  | _ => SOp x op y (Var z)
                  end
              end
          | _ => SOp x op y z
          end in
        match map.get names (rhs_of_stmt simplified) with
        | None => (simplified, map.put names (rhs_of_stmt simplified) x, map.put values x simplified, aliases)
        | Some x' => (SSkip, names, values, map.put aliases x x')
        end
    | SSet x y =>
        let y := get_default aliases y y in
        (SSkip, names, values, map.put aliases x y)
    | SIf cond bThen bElse => (SSkip, map.empty, map.empty, map.empty)
    | SLoop body1 cond body2 => (SSkip, map.empty, map.empty, map.empty)
    | SSeq s1 s2 =>
        let '(s1', names', values', aliases') := lvn' names values aliases s1 in
        let '(s2', names'', values'', aliases'') := lvn' names' values' aliases' s2 in
        (SSeq s1' s2', names'', values'', aliases'')
    | SSkip => (SSkip, names, values, aliases)
    | SCall binds f args => (SSkip, map.empty, map.empty, map.empty)
    | SInteract binds a args => (SSkip, map.empty, map.empty, map.empty)
    end.

  Definition lvn := lvn' map.empty map.empty map.empty.
End VarName.

Definition example1 : stmt Z := SSeq (SSet 2 1) (SLoad access_size.word 3 2 0).

Check (ssa Z Z.ltb Z_strict_order).
Local Notation ssa_ := (ssa Z Z.ltb Z_strict_order).

Definition example1_ssa := fst (ssa_ example1).
Compute example1_ssa.

Local Notation lvn_ := (lvn Z Z.ltb Z_strict_order).
Compute (match example1_ssa with |SSeq a b => a |_ => SSkip end).
Compute (lvn_ example1_ssa).
