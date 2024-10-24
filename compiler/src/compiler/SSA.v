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

(*
  Definition env: map.map String.string Syntax.func := SortedListString.map _.
#[export] Instance env_ok: map.ok env := SortedListString.ok _.

*)

Section VarName.
  Context (varname : Type) {natmap : map.map varname nat}.
  
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
  Check map.map. Print map.map. Search (map.map). Check map.put. Check map.rep.
  Print map.map. Search map.put. Check map.update. Print map.update. Search map.update.
  Check @map.get.
  Existing Instance natmap.
  Definition get := @map.get _ _ natmap.
  Definition getnat (count : map.rep) (x : varname) :=
    match get count x with
    | Some n => n
    | None => O
    end.
  Definition inc (count : map.rep) (x : varname) :=
    map.put count x (getnat count x).
  Print operand.
  Definition label_operand (x : @operand varname) (count : map.rep) :
    @operand (varname * nat) :=
    match x with
    | Var x => Var (x, getnat count x)
    | Const x => Const x
    end.
                     
  Fixpoint ssa' (count : map.rep) (s : stmt varname) :
    stmt (varname * nat) * natmap :=
    match s with
    | SLoad sz x a offset =>
        (SLoad sz (x, S (getnat count x)) (a, getnat count a) offset, inc count x)
    | SStore sz x a offset =>
        (SStore sz (x, S (getnat count x)) (a, getnat count a) offset, inc count x)
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
    | SSkip => (SSkip, map.empty)
    | SCall binds f args => (SSkip, map.empty)
    | SInteract binds a args => (SSkip, map.empty)
    end.

  Definition ssa := ssa' map.empty.

  Context (stmt_to_label : map.map (stmt (varname * nat)) (varname * nat)).
  Context (label_to_label : map.map (varname * nat) (varname * nat)).
  Context (label_to_stmt : map.map (varname * nat) (stmt (varname * nat))).
  (*when we get to *)
  Definition get_default {A B : Type} {mt} m x d :=
    match @map.get A B mt m x with
    | Some y => y
    | None => d
    end.
  (*Note: I treat names as if it is magical in certain ways.
    The domain is actually statements mod some equivalence relation, wheere for example:
    - SLit "1" 1 = SLit "2" 1
    - "z" := "x" + "y" = "ry" = "y" + "x"
    That is, two operations are the same if they're the same.
    I should actually implement this rather than just pretending that it works.
   *)
  Fixpoint lvn (names : stmt_to_label) (values : label_to_stmt)
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
        match map.get names simplified with
        | None => (simplified, map.put names simplified x, map.put values x simplified, aliases)
        | Some x' => (SSkip, names, values, map.put aliases x x')
        end
    | SStackalloc x nbytes body => (SSkip, map.empty, map.empty, map.empty)
    | SLit x v =>
        match map.get names (SLit x v) with
        | None => (SLit x v, map.put names (SLit x v) x, map.put values x (SLit x v), aliases)
        | Some x' => (SSkip, names, values, map.put aliases x x')
        end
    | _ => (SSkip, map.empty, map.empty, map.empty)
    end.
