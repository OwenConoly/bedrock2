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

Fixpoint is_simple {varname : Type} (s : stmt varname) :=
  match s with
  | SLoad _ _ _ _ => true
  | SStore _ _ _ _ => true
  | SInlinetable _ _ _ _ => true
  | SStackalloc _ _ _ => false
  | SLit _ _ => true
  | SOp _ _ _ _ => true
  | SSet _ _ => true
  | SIf _ _ _ => false
  | SLoop _ _ _ => false
  | SSeq s1 s2 => is_simple s1 && is_simple s2
  | SSkip => true
  | SCall _ _ _ => false
  | SInteract _ _ _ => false
  end.

Section RHS.
  Context {varname : Type}.
  Definition as_to_Z (x : access_size) :=
    match x with
    | access_size.one => 0
    | access_size.two => 1
    | access_size.four => 2
    | access_size.word => 3
    end.
  Print stmt.

  Inductive rhs :=
  | RLoad (sz : access_size) (a : varname) (offset : Z)
  | RStore (sz : access_size) (a : varname) (offset : Z)
  | RInlinetable (sz : access_size) (t : list byte) (i : varname)
  | RLit (v : Z)
  (* | RWord (w : word) *)
  | ROp (op : bopname) (y : varname) (z : @operand varname)
  | RSet (y : varname).

  Definition rhs_of_stmt (s : stmt varname) :=
    match s with
    | SLoad sz x a offset => RLoad sz a offset
    | SStore sz x a offset => RStore sz a offset
    | SInlinetable sz x t i => RInlinetable sz t i
    | SLit x v => RLit v
    | SOp x op y z => ROp op y z
    | SSet x y => RSet y
    | _ => RLit 0
    end.
  
  Check SOp.
  Inductive rhs_op :=
  | RLoad_ | RStore_ | RInlinetable_ | RLit_ | ROp_ | RSet_.

  Definition rhs_tuple : Type := rhs_op * option access_size * option varname (*rs1*) * option Z (*imm*) * option (list byte) * option bopname * option (@operand varname).

  Definition rhs_to_tuple (s : rhs) : rhs_tuple :=
    match s with
    | RLoad sz a offset => (RLoad_, Some sz, Some a, Some offset, None, None, None)
    | RStore sz a offset => (RStore_, Some sz, Some a, Some offset, None, None, None)
    | RInlinetable sz t i => (RInlinetable_, Some sz, Some i, None, Some t, None, None)
    | RLit v => (RLit_, None, None, Some v, None, None, None)
    | ROp op y z => (ROp_, None, Some y, None, None, Some op, Some z)
    | RSet y => (RSet_, None, Some y, None, None, None, None)
    end.

  Definition rhsop_to_Z (x : rhs_op) : Z :=
    match x with
    | RLoad_ => 0
    | RStore_ => 1
    | RInlinetable_ => 2
    | RLit_ => 3
    | ROp_ => 4
    | RSet_ => 5
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
  
  Check (lexicog4 (lexicog4 (lift2 rhsop_to_Z Z.ltb) (with_bot (lift2 as_to_Z Z.ltb)) (with_bot lt_varname) (with_bot Z.ltb)) (with_bot (lexicog (lift2 byte.unsigned Z.ltb))) (with_bot (lift2 bopname_to_Z Z.ltb)) (with_bot (lift2 operand_to_tuple (lexicog3 Z.ltb (with_bot lt_varname) (with_bot Z.ltb))))).

  (*I suspect I should be able to make coq do this, given with_bot, lift2, Z.lt, etc.*)
  Definition rhslt : rhs -> rhs -> bool :=
    lift2 rhs_to_tuple (lexicog4 (lexicog4 (lift2 rhsop_to_Z Z.ltb) (with_bot (lift2 as_to_Z Z.ltb)) (with_bot lt_varname) (with_bot Z.ltb)) (with_bot (lexicog (lift2 byte.unsigned Z.ltb))) (with_bot (lift2 bopname_to_Z Z.ltb)) (with_bot (lift2 operand_to_tuple (lexicog3 Z.ltb (with_bot lt_varname) (with_bot Z.ltb))))).

  Lemma rhslt_strict : strict_order rhslt.
  Proof.
    cbv [rhslt].
    repeat (apply lexicog_strict || apply lt_varname_strict || apply lexicog4_strict || apply lexicog3_strict || apply Z_strict_order || apply with_bot_strict || match goal with | |- strict_order (lift2 _ _) => apply lift2_strict end).
    - intros. destruct x, y; simpl in H; reflexivity || congruence.
    - intros. destruct x, y; simpl in H; reflexivity || congruence.
    - exact byte.unsigned_inj.
    - intros. destruct x, y; simpl in H; reflexivity || congruence.
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

  Definition label_to_rhs_parameters : parameters :=
    {| key := varname * nat;
      value := @rhs (varname * nat);
      ltb := label_lt |}.

  Definition label_to_rhs := SortedList.map label_to_rhs_parameters label_lt_strict.

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

  Check exec.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word byte} {localsH: map.map varname word} {envH: map.map String.string (list varname * list varname * stmt varname)}.
  Context {localsL : map.map (varname * nat) word} {envL: map.map String.string (list (varname * nat) * list (varname * nat) * stmt (varname * nat))}.
  Context {localsH_ok : map.ok localsH} {localsL_ok : map.ok localsL}.
  Context {ext_spec: ExtSpec}. Print EqDecider.
  Context {eqd : forall x y : varname, _} {HED : EqDecider eqd}.
  Context {eqd' : forall x y : varname * nat, _} {HED' : EqDecider eqd'}.
  Context (phase : compphase) (isRegH : varname -> bool) (isRegL : varname * nat -> bool).
  Notation execH := (@exec varname _ _ _ _ _ _ _ phase isRegH).
  Notation execL := (@exec (varname * nat)  _ _ _ _ _ _ _ phase isRegL).

  Definition compile_locals (count : varname_to_nat) (lH : localsH) : localsL :=
    map.fold (fun lH k v => map.put lH (k, getnat count k) v) map.empty lH.

  Lemma compile_locals_spec count lH :
    forall k n v, map.get (compile_locals count lH) (k, n) = Some v <->
               n = getnat count k /\ map.get lH k = Some v.
  Proof.
    cbv [compile_locals]. apply map.fold_spec.
    - intros. split.
      + intros H. rewrite map.get_empty in H. discriminate H.
      + intros [_ H]. rewrite map.get_empty in H. discriminate H.
    - intros. rewrite map.get_put_dec. Tactics.destruct_one_match; intros.
    + inversion E. subst. clear E. split.
      -- intros H1. inversion H1. subst. clear H1. split; [reflexivity|].
         apply map.get_put_same.
      -- intros [H1 H2]. rewrite map.get_put_same in H2. apply H2.
    + split.
      -- intros H1. apply H0 in H1. destruct H1 as [? H1]. subst. rewrite map.get_put_diff by congruence.
         auto.
      -- intros [H1 H2]. subst. assert (k0 <> k).
         { intros no. subst. apply E. reflexivity. }
         apply H0. split; auto. rewrite map.get_put_diff in H2 by assumption. assumption.
  Qed.

  Lemma compile_locals_spec' count lH :
    forall k n, map.get (compile_locals count lH) (k, n) =
             if (Nat.eqb n (getnat count k)) then map.get lH k else None.
  Proof.
    intros. destruct (map.get _ _) eqn:E.
    - apply compile_locals_spec in E. destruct E. subst. rewrite Nat.eqb_refl. symmetry. assumption.
    - destruct (Nat.eqb _ _) eqn:En.
      + destruct (map.get lH k) eqn:Eget.
        -- rewrite <- E. apply compile_locals_spec. apply Nat.eqb_eq in En. auto.
        -- reflexivity.
      + reflexivity.
  Qed.

  Lemma compile_locals_spec'' count lH k :
    map.get (compile_locals count lH) (k, getnat count k) = map.get lH k.
  Proof. rewrite compile_locals_spec'. rewrite Nat.eqb_refl. reflexivity. Qed.

  Lemma compile_locals_spec''' count lH k v :
    map.get lH k = Some v ->
    map.get (compile_locals count lH) (k, getnat count k) = Some v.
  Proof. rewrite compile_locals_spec''. auto. Qed.
                                                             
  
  Lemma getnat_inc_same count k : getnat (inc count k) k = S (getnat count k).
  Proof. cbv [getnat inc get]. rewrite map.get_put_same. reflexivity. Qed.

  Lemma getnat_inc_diff count k k' : k' <> k -> getnat (inc count k) k' = getnat count k'.
  Proof.
    intros. cbv [getnat inc get]. rewrite map.get_put_diff by assumption. reflexivity.
  Qed.
  
  Lemma compile_locals_inc count k v lH lL :
    map.extends lL (compile_locals count lH) ->
    map.extends (map.put lL (k, S (getnat count k)) v)
    (compile_locals (inc count k) (map.put lH k v)).
  Proof.
    cbv [map.extends]. intros H x w. rewrite map.get_put_dec. Tactics.destruct_one_match.
    - rewrite compile_locals_spec'. rewrite getnat_inc_same. rewrite Nat.eqb_refl.
      rewrite map.get_put_same. auto.
    - destruct x as [k' n]. intros. erewrite H; [reflexivity|].
      rewrite compile_locals_spec' in *.
      destruct (Nat.eqb _ _) eqn:E'; [apply Nat.eqb_eq in E' | apply Nat.eqb_neq in E']; subst.
      + assert (k' <> k).
        { intros ?. subst. rewrite getnat_inc_same in E. auto. }
        rewrite map.get_put_diff in H0 by assumption.
        rewrite getnat_inc_diff by assumption. rewrite Nat.eqb_refl. auto.
      + congruence.
  Qed.

  Require Import coqutil.Tactics.fwd.
  
  Lemma ssa_works eH eL s t m lH mcH post :
    is_simple s = true ->
    execH eH s t m lH mcH post ->
    forall lL mcL count,
    map.extends lL (compile_locals count lH) ->
    execL eL (fst (ssa' count s)) t m lL mcL
      (fun t' m' lL' mc' =>
         exists lH' mcH',
           post t' m' lH' mcH' /\
             map.extends lL' (compile_locals (snd (ssa' count s)) lH')).
  Proof.
    intros Hsimple Hexec. induction Hexec; intros lL mcL count; try discriminate Hsimple; intros Hext; try (econstructor; eauto using compile_locals_spec'''); try (do 2 eexists; split; [eassumption|]); simpl; try apply compile_locals_inc; try assumption.
    - intros no. inversion no. subst. apply H. reflexivity.
    - cbv [exec.lookup_op_locals] in *.
      cbv [label_operand]. destruct z; eauto using compile_locals_spec'''.
    - simpl in Hsimple. apply andb_prop in Hsimple. destruct Hsimple as [Hsimple1 Hsimple2].
      rewrite Hsimple1, Hsimple2 in *. clear Hsimple1 Hsimple2. simpl.
      specialize (IHHexec eq_refl lL mcL count ltac:(assumption)).
      destruct (ssa' count s1) as [s1' count'].
      specialize H0 with (count := count').
      destruct (ssa' count' s2) as [s2' count'']. simpl in *.
      econstructor; [eassumption|]. simpl. intros. fwd. eapply H0; eauto.
  Qed.
  
  Definition get_default {A B : Type} {mt} m x d :=
    match @map.get A B mt m x with
    | Some y => y
    | None => d
    end.
  
  Fixpoint lvn' (names : rhs_to_label) (values : label_to_rhs)
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
          | Some (RLit c) =>
              let val := 0 (*should actually evaluate the thing*) in SLit x val
          | _ => SInlinetable sz x t i
          end in
        (*check if we've seen this before:
          - if so, update aliases appropriately, and skip
          - otherwise, add to list of names, and don't skip *)
        match map.get names (rhs_of_stmt simplified) with
        | None => (simplified, map.put names (rhs_of_stmt simplified) x, map.put values x (rhs_of_stmt simplified), aliases)
        | Some x' => (SSkip, names, values, map.put aliases x x')
        end
    | SStackalloc x nbytes body => (SSkip, map.empty, map.empty, map.empty)
    | SLit x v =>
        match map.get names (rhs_of_stmt (SLit x v)) with
        | None => (SLit x v, map.put names (rhs_of_stmt (SLit x v)) x, map.put values x (rhs_of_stmt (SLit x v)), aliases)
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
          | Some (RLit c1) =>
              match z with
              | Const c2 => SLit x (word.unsigned (interp_binop op (word.of_Z c1) (word.of_Z c2)))(*TODO: wouldn't have to deal with word-to-nat conversions if i would add a word literal construct*)
              | Var z =>
                  match map.get values z with
                  | Some (RLit c2) => SLit x (word.unsigned (interp_binop op (word.of_Z c1) (word.of_Z c2)))
                  | _ => SOp x op y (Var z)
                  end
              end
          | _ => SOp x op y z
          end in
        match map.get names (rhs_of_stmt simplified) with
        | None => (simplified, map.put names (rhs_of_stmt simplified) x, map.put values x (rhs_of_stmt simplified), aliases)
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

  Print get_default.
  Print rhs. Search bopname. Print operand.
  Definition eval_rhs (l : localsL) (e : @rhs (varname * nat)) : word :=
    match e with
    | RLoad sz a offset => word.of_Z 0
    | RStore sz a offset => word.of_Z 0
    | RInlinetable sz t i => word.of_Z 0 (*fill in*)
    | RLit v => word.of_Z v
    | ROp op y z =>
        let y := get_default l y (word.of_Z 0) in
        let z :=
          match z with
          | Const z => word.of_Z z
          | Var z => get_default l z (word.of_Z 0)
          end in
        interp_binop op y z
    | RSet x => get_default l x (word.of_Z 0)
    end. Check @rhs_of_stmt.

  Definition names_values_aliases_good (used_before : list (varname * nat)) (lH lL : localsL) (names : rhs_to_label) (values : label_to_rhs) (aliases : label_to_label) :=
    (*lH related to lL via aliases*)
    (forall x y, map.get lH x = Some y ->
           (*map.get lH (get_default aliases x x) = Some y, but do we care?*)
            map.get lL (get_default aliases x x) = Some y) /\
      (*values related to lL*)
      (forall x e, map.get values x = Some e -> map.get lH x = Some (eval_rhs lH e)) /\
      (*names related to lL*)
      (forall x e, map.get names e = Some x -> map.get lH x = Some (eval_rhs lH e)) /\
      (forall x y, map.get aliases x = Some y -> In y used_before).
  
  (*forall (e : rhs),
    map.get values (get_default aliases x x) = Some e ->
    map.get names e = Some (get_default aliases x x) /\
    eval_rhs lL e = y.*)

  Definition used_in (s : stmt)

  Lemma lvn_works e sH t m lH mcH post used_before :
    is_simple sH = true ->
    
    execL e sH t m lH mcH post ->
    forall lL mcL names values aliases,
    names_values_aliases_good lH lL names values aliases ->
    let '(sL, names', values', aliases') := lvn' names values aliases sH in
    execL e sL t m lL mcL
      (fun t' m' lL' mc' =>
         exists lH' mcH',
           post t' m' lH' mcH' /\
             names_values_aliases_good lH' lL' names' values' aliases'
                     
             (*(forall x y, map.get aliases x = Some y -> map.get lH' x = map.get lH' y) /\*)
             (*(forall x y, map.get values x = Some y -> map.get lH' x = Some (eval_rhs lH' y))*)
      ).
  Proof.
    intros Hsimple Hexec. induction Hexec; cbn [lvn']; intros lL mcL names values aliases (Hgood1 & Hgood2 & Hgood3); try discriminate Hsimple.
    - apply Hgood1 in H. econstructor; eauto. do 2 eexists. split; [eassumption|].
      cbv [names_values_aliases_good]. ssplit.
      + intros x0 y0. rewrite map.get_put_dec. Tactics.destruct_one_match.
        -- intros Hx0. inversion Hx0. subst. rewrite map.get_put_same. reflexivity.
        -- intros Hx0. apply Hgood1 in Hx0. rewrite map.get_put_diff by assumption.
      intros x0 y0. specialize (Hgood x0 y0).
      rewrite map.get_put_dec. Tactics.destruct_one_match.
      + intros H. inversion H. subst. rewrite map.get_put_same. split; [reflexivity|].
        intros. eexists. clear H.
      + simpl.
      apply do 2 eexists. split; [eassumption|].

  
End VarName.

Definition example1 : stmt Z := SSeq (SSet 2 1) (SLoad access_size.word 3 2 0).

Check (ssa Z Z.ltb Z_strict_order).
Local Notation ssa_ := (ssa Z Z.ltb Z_strict_order).

Definition example1_ssa := fst (ssa_ example1).
Compute example1_ssa.

Local Notation lvn_ := (lvn Z Z.ltb Z_strict_order).
Compute (match example1_ssa with |SSeq a b => a |_ => SSkip end).
Compute (lvn_ example1_ssa).
