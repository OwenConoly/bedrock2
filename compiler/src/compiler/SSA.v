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
Require Import coqutil.Tactics.fwd.
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
  | SLoad _ _ _ _ => True
  | SStore _ _ _ _ => True
  | SInlinetable _ _ _ _ => True
  | SStackalloc _ _ _ => False
  | SLit _ _ => True
  | SOp _ _ _ _ => True
  | SSet _ _ => True
  | SIf _ _ _ => False
  | SLoop _ _ _ => False
  | SSeq s1 s2 => is_simple s1 /\ is_simple s2
  | SSkip => True
  | SCall _ _ _ => False
  | SInteract _ _ _ => False
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

  Definition varname_to_nat_parameters : parameters :=
    {| key := varname;
      value := nat;
      ltb := varname_lt |}.

  Definition varname_to_nat := SortedList.map varname_to_nat_parameters varname_lt_strict.
  
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

  
  Lemma ssa_works eH eL s t m lH mcH post :
    is_simple s ->
    execH eH s t m lH mcH post ->
    forall lL mcL count,
    map.extends lL (compile_locals count lH) ->
    execL eL (fst (ssa' count s)) t m lL mcL
      (fun t' m' lL' mc' =>
         exists lH' mcH',
           post t' m' lH' mcH' /\
             map.extends lL' (compile_locals (snd (ssa' count s)) lH')).
  Proof.
    intros Hsimple Hexec. induction Hexec; intros lL mcL count; try solve [destruct Hsimple]; intros Hext; try (econstructor; eauto using compile_locals_spec'''); try (do 2 eexists; split; [eassumption|]); simpl; try apply compile_locals_inc; try assumption.
    - intros no. inversion no. subst. apply H. reflexivity.
    - cbv [exec.lookup_op_locals] in *.
      cbv [label_operand]. destruct z; eauto using compile_locals_spec'''.
    - destruct Hsimple as [Hsimple1 Hsimple2].
      specialize (IHHexec ltac:(assumption) lL mcL count ltac:(assumption)).
      destruct (ssa' count s1) as [s1' count'].
      specialize H0 with (count := count').
      destruct (ssa' count' s2) as [s2' count'']. simpl in *.
      econstructor; [eassumption|]. simpl. intros. fwd. eapply H0; eauto.
  Qed.
End VarName.

Section LVN.
  Context (varname : Type).
  Context (varname_lt : varname -> varname -> bool).
  Context (varname_lt_strict : strict_order varname_lt).
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word byte} {locals: map.map varname word} {env: map.map String.string (list varname * list varname * stmt varname)}.
  Context {locals_ok : map.ok locals}.
  Context {ext_spec: ExtSpec}. Print EqDecider.
  Context {eqd : forall x y : varname, _} {HED : EqDecider eqd}.
  Context {eqd' : forall x y : @rhs varname, _} {HED' : EqDecider eqd'}.
  Context (phase : compphase) (isReg : varname -> bool).
  
  Notation exec := (@exec varname _ _ _ _ _ _ _ phase isReg).
    
  (*Let rhs_to_label_parameters : parameters :=
    {| key := rhs;
      ltb := rhslt varname_lt;
      value := varname|}.

  Definition rhslabel_strict :
    strict_order rhs_to_label_parameters.(ltb).
  Proof.
    apply rhslt_strict. apply varname_lt_strict.
  Defined.

  Check (SortedList.map rhs_to_label_parameters rhslabel_strict).

  Definition rhs_to_label := SortedList.map rhs_to_label_parameters rhslabel_strict.
  
  Let label_to_label_parameters : parameters :=
    {| key := varname;
      value := varname;
      ltb := varname_lt |}.

  Definition label_to_label := SortedList.map label_to_label_parameters varname_lt_strict.

  Let label_to_rhs_parameters : parameters :=
    {| key := varname;
      value := @rhs varname;
      ltb := varname_lt |}.

  Definition label_to_rhs := SortedList.map label_to_rhs_parameters varname_lt_strict.*)
  
  Context (rhs_to_label : map.map (@rhs varname) varname).
  Context (label_to_label : map.map varname varname).
  Context (label_to_rhs : map.map varname (@rhs varname)).
  Context {rhs_to_label_ok : map.ok rhs_to_label}.
  Context {label_to_label_ok : map.ok label_to_label}.
  Context {label_to_rhs_ok : map.ok label_to_rhs}.
  Context {word_ok : word.ok word}.
  
  Definition get_default {A B : Type} {mt} m x d :=
    match @map.get A B mt m x with
    | Some y => y
    | None => d
    end.
  
  Fixpoint lvn' (names : rhs_to_label) (values : label_to_rhs)
    (aliases : label_to_label) (s : stmt varname) :=
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
    | SStore sz a v offset =>
        let a := get_default aliases a a in
        let v := get_default aliases v v in
        (SStore sz a v offset, names, values, aliases)
    | SInlinetable sz x t i =>
        (*canonical names*)
        let i := get_default aliases i i in
        (*simplify*)
        let simplified :=
          match map.get values i with
          | Some (RLit c) =>
              let val :=
                match load sz (map.of_list_word t) (word.of_Z c) with
                | Some val => val
                | None => word.of_Z 0
                end
              in SLit x (word.unsigned val)
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
  Print exec.exec.
  
  Definition eval_rhs(*_with_aliases*) (*(aliases : label_to_label)*) (l : locals) (e : @rhs varname) : word :=
    match e with
    | RLoad sz a offset => word.of_Z 0
    | RStore sz a offset => word.of_Z 0
    | RInlinetable sz t i =>
        (*let i := get_default aliases i i in*)
        match load sz (map.of_list_word t) (get_default l i (word.of_Z 0)) with
        | Some val => val
        | None => word.of_Z 0
        end
    | RLit v => word.of_Z v
    | ROp op y z =>
        (*let y := get_default aliases y y in*)
        let y := get_default l y (word.of_Z 0) in
        let z :=
          match z with
          | Const z => word.of_Z z
          | Var z => (*let z := get_default aliases z z in*)
                    get_default l z (word.of_Z 0)
          end in
        interp_binop op y z
    | RSet x => (*let x := get_default aliases x x in*)
               get_default l x (word.of_Z 0)
    end.

  (*Definition eval_rhs := eval_rhs_with_aliases map.empty.*)

  Definition names_values_aliases_good (lH lL : locals) (names : rhs_to_label) (values : label_to_rhs) (aliases : label_to_label) :=
    (*lH related to lL via aliases*)
    (forall x y, map.get lH x = Some y ->
            map.get lL (get_default aliases x x) = Some y) /\
      (*values related to lL*)
      (forall x e, map.get values x = Some e -> map.get lL x = Some (eval_rhs lL e)) /\
      (*names related to lL*)
      (forall x e, map.get names e = Some x -> map.get lL x = Some (eval_rhs lL e)).
  
  (*forall (e : rhs),
    map.get values (get_default aliases x x) = Some e ->
    map.get names e = Some (get_default aliases x x) /\
    eval_rhs lL e = y.*)

  Print stmt.
  Fixpoint modified_in (name : varname) (s : stmt varname) : Prop :=
    match s with
    | SLoad sz x a offset => name = x
    | SStore sz x a offset => name = x
    | SInlinetable sz x t i => name = x
    | SLit x v => name = x
    | SOp x op y z => name = x
    | SSet x y => name = x
    | SSeq s1 s2 => modified_in name s1 \/ modified_in name s2
    | SSkip => False
    | _ => True
    end.

  (* (*could define by using accessed*) *)
  (* Fixpoint accessed_in (name : varname) (s : stmt varname) : Prop := *)
  (*   match s with *)
  (*   | SLoad sz x a offset => name = a  *)
  (*   | SStore sz x a offset => name = x \/ name = a *)
  (*   | SInlinetable sz x t i => name = i *)
  (*   | SLit x v => False *)
  (*   | SOp x op y z => name = y \/ z = Var name *)
  (*   | SSet x y => name = y *)
  (*   | SSeq s1 s2 => accessed_in name s1 \/ accessed_in name s2 *)
  (*   | SSkip => False *)
  (*   | _ => True *)
  (*   end. *)

  Fixpoint in_rhs (name : varname) (e : rhs) : Prop :=
    match e with
    | RLoad sz a offset => name = a
    | RStore sz a offset => name = a
    | RInlinetable sz t i => name = i
    | RLit v => False
    | ROp op y z => name = y \/ Var name = z
    | RSet y => name = y
    end.

  Lemma not_in_rhs_irrelevant x y l e :
    ~in_rhs x e ->
    eval_rhs (map.put l x y) e = eval_rhs l e.
  Proof.
    intros H. destruct e; simpl in *; try reflexivity.
    - cbv [get_default]. rewrite map.get_put_diff by auto.
      reflexivity.
    - assert (H0: y0 <> x /\ z <> Var x) by auto. clear H. destruct H0 as [H1 H2].
      cbv [get_default]. rewrite map.get_put_diff by auto.
      destruct z; [|reflexivity]. assert (v <> x) by congruence.
      rewrite map.get_put_diff by auto.
      reflexivity.
    - cbv [get_default]. rewrite map.get_put_diff by auto.
      reflexivity.
  Qed.

  Definition ssa_hyps_aliases x (aliases : label_to_label) :=
    (map.get aliases x = None) /\
      (forall y, map.get aliases y <> Some x).

  Definition ssa_hyps_values x (values : label_to_rhs) :=
    (map.get values x = None) /\
      (forall y e, map.get values y = Some e -> ~in_rhs x e).

  Definition ssa_hyps_names x (names : rhs_to_label) :=
    (forall y e, map.get names e = Some y -> ~in_rhs x e) /\
    (forall e, map.get names e <> Some x).
  
  Definition ssa_hyps x names values aliases :=
    ssa_hyps_aliases x aliases /\
     ssa_hyps_values x values /\
      ssa_hyps_names x names.

  Lemma put_both lH lL x names values aliases r :
    ssa_hyps x names values aliases ->
    names_values_aliases_good lH lL names values aliases ->
    ~in_rhs x r ->
    (*eval_rhs lH r1 = eval_rhs lL r2 ->*)
    names_values_aliases_good (map.put lH x (eval_rhs lL r)) (map.put lL x (eval_rhs lL r)) (map.put names r x) (map.put values x r) aliases.
  Proof.
    intros [[ssa_aliases_l  ssa_aliases_r] [[ssa_values_l ssa_values_r] [ssa_names_l ssa_names_r]]] (Hgood1 & Hgood2 & Hgood3) notin.
    split; [|split].
    - intros x0 y0. rewrite map.get_put_dec. destruct_one_match.
      + intros Hx0. inversion Hx0. subst. 
        cbv [get_default]. rewrite ssa_aliases_l. rewrite map.get_put_same. reflexivity.
      + intros Hx0. apply Hgood1 in Hx0. rewrite <- Hx0. apply map.get_put_diff.
        cbv [get_default]. destruct_one_match.
        -- intros H'. subst. apply ssa_aliases_r in E0. apply E0.
        -- congruence.
    - intros x0 e0. rewrite map.get_put_dec. destruct_one_match.
      ++ simpl. intros Hx0. inversion Hx0. subst e0. clear Hx0.
         rewrite map.get_put_same. rewrite not_in_rhs_irrelevant by assumption.
         reflexivity.
      ++ (*load*) intros Hx0.
         rewrite map.get_put_diff by auto.
         specialize Hgood2 with (1 := Hx0). rewrite Hgood2.
         rewrite not_in_rhs_irrelevant. 1: reflexivity.
         eapply ssa_values_r. apply Hx0.
    - intros x0 e0. rewrite map.get_put_dec. destruct_one_match.
      + simpl. intros Hx0. inversion Hx0. subst x0. clear Hx0.
         rewrite map.get_put_same. rewrite not_in_rhs_irrelevant by assumption.
         reflexivity.
      + intros Hx0. rewrite map.get_put_diff.
        -- rewrite not_in_rhs_irrelevant.
           ++ apply Hgood3. assumption.
           ++ eapply ssa_names_l. eassumption.
        -- intros H'. subst x0. eapply ssa_names_r. eassumption.
  Qed.

  Lemma put_both_and_forget lH lL x v names values aliases :
    ssa_hyps x names values aliases ->
     names_values_aliases_good lH lL names values aliases ->
     names_values_aliases_good (map.put lH x v) (map.put lL x v) names values aliases.
   Proof.  
    intros [[ssa_aliases_l  ssa_aliases_r] [[ssa_values_l ssa_values_r] [ssa_names_l ssa_names_r]]] (Hgood1 & Hgood2 & Hgood3).
    split; [|split].
    - intros x0 y0. rewrite map.get_put_dec. destruct_one_match.
      + intros Hx0. inversion Hx0. subst. 
        cbv [get_default]. rewrite ssa_aliases_l. rewrite map.get_put_same. reflexivity.
      + intros Hx0. apply Hgood1 in Hx0. rewrite <- Hx0. apply map.get_put_diff.
        cbv [get_default]. destruct_one_match.
        -- intros H'. subst. apply ssa_aliases_r in E0. apply E0.
        -- congruence.
    - intros x0 e0 Hx0. assert (x0 <> x).
      { intros H'. subst.
        rewrite ssa_values_l in Hx0. congruence. }
      rewrite map.get_put_diff by assumption.
      specialize ssa_values_r with (1 := Hx0). apply Hgood2 in Hx0.
      rewrite not_in_rhs_irrelevant by assumption. assumption.
    - intros x0 e0 Hx0. specialize Hgood3 with (1 := Hx0).
      specialize ssa_names_l with (1 := Hx0).
      assert (x0 <> x).
      { intros H'. subst.
        apply ssa_names_r in Hx0. assumption. }
      rewrite map.get_put_diff by assumption.
      rewrite not_in_rhs_irrelevant by assumption. assumption.
   Qed.
   
  Lemma put_high lH lL x y v names values aliases r :
    ssa_hyps y names values aliases ->
    names_values_aliases_good lH lL names values aliases ->
    eval_rhs lL r = v ->
    map.get names r = Some x ->
    names_values_aliases_good (map.put lH y v) lL names values (map.put aliases y x).
  Proof.
    intros [[ssa_aliases_l  ssa_aliases_r] [[ssa_values_l ssa_values_r] [ssa_names_l ssa_names_r]]] (Hgood1 & Hgood2 & Hgood3) Heval Hnames.
    split; [|split].
    - intros x0 y0. rewrite map.get_put_dec. destruct_one_match.
      + intros Hy0. inversion Hy0. subst. cbv [get_default].
        rewrite map.get_put_same. apply Hgood3 in Hnames. rewrite Hnames.
        reflexivity.
      + intros Hy0. cbv [get_default]. rewrite map.get_put_diff by auto.
        apply Hgood1. assumption.
    - apply Hgood2.
    - apply Hgood3.
  Qed.

  Lemma const_prop lH lL x val names values aliases :
    ssa_hyps x names values aliases ->
    names_values_aliases_good lH lL names values aliases ->
    names_values_aliases_good (map.put lH x (word.of_Z val))
      (map.put lL x (word.of_Z val)) (map.put names (rhs_of_stmt (SLit x val)) x)
      (map.put values x (rhs_of_stmt (SLit x val))) aliases.
  Proof.
    intros [[ssa_aliases_l  ssa_aliases_r] [[ssa_values_l ssa_values_r] [ssa_names_l ssa_names_r]]] (Hgood1 & Hgood2 & Hgood3).
    split; [|split].
    - intros x0 y0. rewrite map.get_put_dec. destruct_one_match.
      + intros Hy0. inversion Hy0. subst y0. cbv [get_default].
        rewrite ssa_aliases_l. apply map.get_put_same.
      + (*this case copied and pasted from put_both*)
        intros Hx0. apply Hgood1 in Hx0. rewrite <- Hx0. apply map.get_put_diff.
        cbv [get_default]. Tactics.destruct_one_match.
        -- intros H'. subst. apply ssa_aliases_r in E0. apply E0.
        -- congruence.
    - intros x0 y0. rewrite map.get_put_dec. destruct_one_match.
      + intros Hy0. inversion Hy0. subst y0. clear Hy0.
        rewrite map.get_put_same. simpl. reflexivity.
      + (*copied and pasted from put_both*)
        intros Hx0. rewrite map.get_put_diff by auto.
        specialize ssa_values_r with (1 := Hx0). apply Hgood2 in Hx0.
        rewrite not_in_rhs_irrelevant by assumption. assumption.
    - intros x0 e0. rewrite map.get_put_dec. destruct_one_match.
      + intros Hx0. inversion Hx0. subst x. rewrite map.get_put_same. reflexivity.
      + intros Hx0. simpl in E. 
        simpl. specialize Hgood3 with (1 := Hx0).
        specialize ssa_names_l with (1 := Hx0).
        rewrite not_in_rhs_irrelevant by assumption.
        assert (x <> x0).
        { intros H'. subst x. eapply ssa_names_r. apply Hx0. }
        rewrite map.get_put_diff by auto. apply Hgood3.
  Qed.

  Fixpoint assigned_to (s : stmt varname) : list varname :=
    match s with
    | SLoad sz x a offset => [x]
    | SStore sz x a offset => [x]
    | SInlinetable sz x t i => [x]
    | SLit x v => [x]
    | SOp x op y z => [x]
    | SSet x y => [x]
    | SSeq s1 s2 => assigned_to s1 ++ assigned_to s2
    | _ => []
    end.

  Lemma modified_assigned_to x s :
    is_simple s ->
    modified_in x s ->
    In x (assigned_to s).
  Proof.
    clear.
    induction s; try (simpl; solve [auto]).
    simpl. intros H1 H2. Search (In _ (_ ++ _)). apply in_app_iff. tauto.
  Qed.

  Lemma modified_once x s1 s2 :
    is_simple (SSeq s1 s2) ->
    NoDup (assigned_to (SSeq s1 s2)) ->
    modified_in x s1 ->
    modified_in x s2 ->
    False.
  Proof.
    intros simple nd m1 m2. apply List.NoDup_app_iff in nd. fold (assigned_to s2).
    simpl in simple. fwd.
    apply modified_assigned_to in m1, m2; [|assumption | assumption].
    eapply ndp3; eassumption.
  Qed.

  Lemma growing_aliases_preserves_ssa_hyps s1 s2 y v names values aliases :
    is_simple (SSeq s1 s2) ->
    NoDup (assigned_to (SSeq s1 s2)) ->
    (forall x, modified_in x (SSeq s1 s2) -> ssa_hyps x names values aliases) ->
    modified_in y s1 ->
    ~modified_in v s2 ->
    (forall x, modified_in x s2 -> ssa_hyps x names values (map.put aliases y v)).
  Proof.
    intros simple ssa_form ssa ymod vnmod x Hx. cbv [ssa_hyps].
    assert (ssax := ssa x (or_intror Hx)).
    destruct ssax as [[ssax_aliases_l  ssax_aliases_r] [ssax_values ssax_names]].
    ssplit.
    - split.
      + rewrite map.get_put_diff.
        { assumption. }
        intros H'. subst. eapply modified_once; eassumption.
      + intros y0. rewrite map.get_put_dec. destruct_one_match.
        -- intros H'. inversion H'. subst. apply vnmod. apply Hx.
        -- auto.
    - assumption.
    - assumption.
  Qed.

  Definition is_assignment (s : stmt varname) : Prop :=
    match s with
    | SLoad sz x a offset => True
    | SStore sz x a offset => True
    | SInlinetable sz x t i => True
    | SLit x v => True
    | SOp x op y z => True
    | SSet x y => True
    | SSeq s1 s2 => False
    | _ => False
    end.

  Fixpoint accessed_in (x : varname) (s : stmt varname) : Prop :=
    match s with
    | SSeq s1 s2 => accessed_in x s1 \/ accessed_in x s2
    | _ => is_assignment s /\ in_rhs x (rhs_of_stmt s)
    end.

  Lemma ass_rhs_accessed s x :
    is_assignment s ->
    in_rhs x (rhs_of_stmt s) ->
    accessed_in x s.
  Proof.
    intros ass rhs. destruct s; simpl in ass; try solve [destruct ass];
      simpl in rhs; subst; simpl; auto.
  Qed.    

  Lemma growing_names_preserves_ssa_hyps s1 s2 y names values aliases :
    is_simple (SSeq s1 s2) ->
    is_assignment s1 ->
    (forall x, modified_in x s2 -> ~accessed_in x s1) ->
    (forall x, modified_in x s2 -> ssa_hyps x names values aliases) ->
    ~modified_in y s2 ->
    (forall x, modified_in x s2 -> ssa_hyps x (map.put names (rhs_of_stmt s1) y) (map.put values y (rhs_of_stmt s1)) aliases).
  Proof.
    intros simple ass ssa_form1 ssa ynmod x Hx. cbv [ssa_hyps].
    assert (ssax := ssa x Hx).
    destruct ssax as [ssax_aliases [[ssax_values_l ssax_values_r] [ssax_names_l ssax_names_r]]].
    ssplit.
    - assumption.
    - split.
      + rewrite map.get_put_diff. 1: assumption. intros H'. subst. auto.
      + intros y0 e. rewrite map.get_put_dec. destruct_one_match.
        -- intros E. inversion E. subst. clear E. apply ssa_form1 in Hx.
           intros H'. apply Hx. apply ass_rhs_accessed; assumption.
        -- intros H. eapply ssax_values_r. eassumption.
     - split.
      + intros y0 e. rewrite map.get_put_dec. destruct_one_match.
        -- intros E. inversion E. subst. clear E. apply ssa_form1 in Hx.
           intros H'. apply Hx. apply ass_rhs_accessed; assumption.
        -- intros H. eapply ssax_names_l. eassumption.
      + intros e. rewrite map.get_put_dec. destruct_one_match.
        -- intros H'. inversion H'. subst. auto.
        -- auto.
  Qed.
  
  Lemma ssa_hyps_preserved s1 s2 names values aliases :
    is_simple (SSeq s1 s2) ->
    NoDup (assigned_to (SSeq s1 s2)) ->
    (forall x, modified_in x s2 -> ~accessed_in x s1) ->
    (forall x, modified_in x (SSeq s1 s2) -> ssa_hyps x names values aliases) ->
    let '(s1', names', values', aliases') := lvn' names values aliases s1 in
    (forall x, modified_in x s2 -> ssa_hyps x names' values' aliases').
  Proof.
    induction s1; intros simple ssa_form1 ssa_form2 ssa; try tauto;
      try (destruct simple as [simple _]; solve [destruct simple]);
      assert (ssa_form' := ssa_form1); simpl in ssa_form'; inversion ssa_form'; subst;
      assert (ssa' := ssa);
      destruct (lvn' names values aliases _) as [[[s1' names'] values'] aliases'] eqn:E;
      cbn -[rhs_of_stmt] in E;
      try (intros x0 H; specialize (ssa x0); specialize (ssa (or_intror H)));
      assert (ssa'':=ssa);
      try destruct ssa'' as [[ssa_aliases_l ssa_aliases_r] [[ssa_values_l ssa_values_r] [ssa_names_l ssa_names_r]]];
      try (inversion E; subst; clear E; assumption).
    - revert E. destruct_one_match.
      + intros E'. inversion E'. subst. clear E'.
        eapply growing_aliases_preserves_ssa_hyps; eauto.
        -- simpl. reflexivity.
        -- specialize (ssa' v). simpl in ssa'. intros H'.
           specialize (ssa' (or_intror H')). clear -H' E ssa'.
           destruct ssa'. destruct H0. clear H H0. destruct H1.
           eapply H0. eapply E.
      + intros E'. inversion E'. subst. clear E'. fwd.
        eapply (growing_names_preserves_ssa_hyps _ s2); simpl; eauto.
        -- destruct simple. split; [|assumption]. repeat destruct_one_match; reflexivity.
        -- repeat destruct_one_match; reflexivity.
        -- intros. assert (H0' := ssa_form2 _ H0).
           simpl in H0'. assert (x1 <> i) by tauto. clear H0'.
           eapply or_intror in H0. apply ssa' in H0. destruct H0 as [H0 _].
           destruct H0 as [_ H0].
           assert (H': x1 <> get_default aliases' i i).
           { cbv [get_default]. destruct_one_match.
             - intros H'. subst. eapply H0. eapply E0.
             - assumption. }
           repeat destruct_one_match; simpl; tauto.
        -- intros. apply ssa'. right. assumption.
        -- intros H'. eapply modified_once; eauto. reflexivity.
    - revert E. destruct_one_match.
      + intros E'. inversion E'. subst. clear E'.
        eapply (growing_aliases_preserves_ssa_hyps _ s2); eauto. 1: reflexivity.
        intros H'. eapply or_intror in H'. apply ssa' in H'. destruct H' as [_ H'].
        destruct H' as [_ H']. destruct H' as [_ H']. apply H' in E. apply E.
      + intros E'. inversion E'. subst. clear E'.
        replace (RLit v) with (rhs_of_stmt (SLit x v)) by reflexivity.
        eapply (growing_names_preserves_ssa_hyps _ s2); eauto.
        -- reflexivity.
        -- intros. apply ssa'. right. assumption.
        -- intros H'. eapply modified_once; eauto. reflexivity.
    - revert E. destruct_one_match.
      + intros E'. inversion E'. subst. clear E'.
        eapply growing_aliases_preserves_ssa_hyps; eauto.
        -- simpl. reflexivity.
        -- specialize (ssa' v). simpl in ssa'. intros H'.
           specialize (ssa' (or_intror H')). clear -H' E ssa'.
           destruct ssa'. destruct H0. clear H H0. destruct H1.
           eapply H0. eapply E.
      + intros E'. inversion E'. subst. clear E'. fwd.
        eapply (growing_names_preserves_ssa_hyps _ s2); simpl; eauto.
        -- destruct simple. split; [|assumption]. repeat destruct_one_match; reflexivity.
        -- repeat destruct_one_match; reflexivity.
        -- intros. assert (H0' := ssa_form2 _ H0).
           simpl in H0'. assert (x1 <> y) by tauto. assert (Var x1 <> z) by tauto.
           clear H0'.
           eapply or_intror in H0. apply ssa' in H0. destruct H0 as [H0 _].
           destruct H0 as [_ H0].
           assert (H': x1 <> get_default aliases' y y).
           { cbv [get_default]. destruct_one_match.
             - intros H'. subst. eapply H0. eapply E0.
             - assumption. }
           assert (H'': match z with
                        | Var z0 => x1 <> get_default aliases' z0 z0
                        | _ => True
                        end).
           { cbv [get_default]. destruct_one_match. 2: reflexivity. destruct_one_match.
             - intros H''. subst. eapply H0. eapply E0.
             - intros H''. subst. congruence. }
           (*assert (thing1: forall x y, @Var varname x = Const y <-> False).
           { intros. split. 2: intros thing; destruct thing.
             intros thing; inversion thing. }*)
           assert (thing2: forall x y, @Var varname x = Var y <-> x = y).
           { intros. split. 2: intros; subst; reflexivity.
             intros thing; inversion thing; subst; reflexivity. }
           destruct z; repeat destruct_one_match; simpl.
           all: try tauto.
           (*all: try rewrite thing1.
           all: try tauto.*)
           all: try rewrite thing2.
           all: tauto.
        -- intros. apply ssa'. right. assumption.
        -- intros H'. eapply modified_once; try eassumption. reflexivity.
    - inversion E. subst. clear E.
      eapply (growing_aliases_preserves_ssa_hyps _ s2); eauto.
      + reflexivity.
      + intros H'. assert (H'' := H'). eapply or_intror in H''.
        apply ssa' in H''. cbv [get_default] in H''.
        revert H''. destruct_one_match.
        -- intros [[_ H''] [[_ _] [_ _]]]. apply H'' in E. apply E.
        -- intros _. apply ssa_form2 in H'. apply H'. cbv [get_default].
           rewrite E. simpl. auto.
    - admit.
    - 
      
  Lemma lvn_works e sH t m lH mcH post :
    is_simple sH ->
    NoDup (assigned_to sH) ->
    exec e sH t m lH mcH post ->
    forall lL mcL names values aliases,
      (forall x, modified_in x sH -> ssa_hyps x names values aliases) ->
      names_values_aliases_good lH lL names values aliases ->
      let '(sL, names', values', aliases') := lvn' names values aliases sH in
      exec e sL t m lL mcL
        (fun t' m' lL' mc' =>
           exists lH' mcH',
             post t' m' lH' mcH' /\
               names_values_aliases_good lH' lL' names' values' aliases').
  Proof.
    intros simple ssa_form Hexec. induction Hexec; cbn [lvn']; intros lL mcL names values aliases ssa nva; try solve [destruct simple];
      try specialize (ssa _ eq_refl); assert (ssa' := ssa); try destruct ssa' as (ssa_aliases_l & ssa_aliases_r & ssa_values_l & ssa_values_r & ssa_names_l & ssa_names_r);
      assert (nva' := nva); destruct nva' as (Hgood1 & Hgood2 & Hgood3).
    - apply Hgood1 in H. econstructor; eauto. do 2 eexists. split; [eassumption|].
       apply put_both_and_forget. 1: assumption. split; [|split]; assumption.
    - apply Hgood1 in H. apply Hgood1 in H0. econstructor; eauto.
    - set (yes_or_no := fun P => P \/ ~P).
      assert (H4: yes_or_no (exists v0, map.get values (get_default aliases i i) = Some (RLit v0))).
      { subst yes_or_no. destruct (map.get values (get_default aliases i i)).
        2: { right. intros ?. fwd. congruence. }
        destruct r; try (right; intros ?; fwd; congruence; left).
        left. eexists. reflexivity. }
      subst yes_or_no.
      assert (H0' := Hgood1). specialize H0' with (1 := H0).
      remember (match map.get values (get_default aliases i i) with
          | Some (RLit _) => _
          | _ => SInlinetable sz x table (get_default aliases i i)
          end) as simplified eqn:Hs.
      assert (eval_rhs lL (rhs_of_stmt simplified) = eval_rhs l (rhs_of_stmt (SInlinetable sz x table i))).
      { simpl. destruct H4 as [yes | no].
        - fwd. simpl. Search v0. apply Hgood2 in yes. cbv [get_default]. rewrite H0.
          rewrite word.of_Z_unsigned. rewrite yes in H0'.
          inversion H0'. subst. reflexivity.
        - assert (simplified = SInlinetable sz x table (get_default aliases i i)).
          { rewrite Hs. destruct_one_match; try reflexivity.
            destruct_one_match; try reflexivity. exfalso. apply no.
            eexists. reflexivity. }
          clear Hs. subst. simpl. cbv [get_default]. fold (get_default aliases i i).
          rewrite H0. rewrite H0'. reflexivity. }
      destruct (map.get names (rhs_of_stmt simplified)) eqn:E; simpl.
      + (*it was already there, so skip*)
        clear Hs. econstructor. do 2 eexists. split; [eassumption|].
        eapply put_high; try eassumption. rewrite H3. simpl.
        cbv [get_default]. rewrite H0, H1. reflexivity.
      + destruct H4 as [yes | no].
        -- (*constant propagation*)
          destruct yes as [v0 yes]. rewrite yes in Hs. rewrite Hs in *. clear Hs.
          remember (word.unsigned _) as val.
          apply Hgood2 in yes. simpl in yes. Search i. simpl in H3.
          cbv [get_default] in H3. rewrite H0 in H3. rewrite H1 in H3. subst v.
          econstructor.
          do 2 eexists. split; [eassumption|]. clear E. apply const_prop; assumption.
        -- (*no constant propagation*)
          assert (simplified = SInlinetable sz x table (get_default aliases i i)).
          { rewrite Hs. destruct_one_match; try reflexivity.
            destruct_one_match; try reflexivity. exfalso. apply no.
            eexists. reflexivity. }
          clear Hs. subst simplified. econstructor; eauto.
          { cbv [get_default]. destruct_one_match.
            - intros H'. eapply ssa_aliases_r. subst x. apply E0.
            - assumption. }
          do 2 eexists. split; [eassumption|]. eassert (v = _) as ->.
          2: { apply put_both; auto. simpl. cbv [get_default].
               destruct_one_match. 2: solve [auto].
               intros H'. subst v0. apply ssa_aliases_r in E0.
               assumption. }
          rewrite H3. simpl. Search i. cbv [get_default]. rewrite H0.
          rewrite H1. reflexivity.
    - simpl. destruct (map.get names _) eqn:E.
      + econstructor. do 2 eexists. split; [eassumption|].
        eapply put_high; try eassumption. simpl. reflexivity.
      + econstructor. do 2 eexists. split; [eassumption|].
        eassert (word.of_Z v = _) as ->. 2: eapply put_both; try eassumption.
        { reflexivity. }
        simpl. tauto.
    - admit.
    - econstructor; eauto. do 2 eexists. split; [eassumption|]. admit.
    - assert (ssa_form' := ssa_form). assert (simple' := simple).
      simpl in simple', ssa_form'.
      apply List.NoDup_app_iff in ssa_form'. fwd.
      specialize (IHHexec ltac:(assumption) ltac:(assumption) lL mcL names values aliases).
      eassert (H': _). 2: specialize (IHHexec H').
      { intros. apply ssa. simpl. left. assumption. }
      specialize (IHHexec ltac:(assumption)).
      assert (ssa_hyps' := ssa_hyps_preserved _ _ _ _ _ ltac:(eassumption) ltac:(eassumption) ltac:(eassumption)).
      destruct (lvn' names values aliases s1) as [ [ [s1' names'] values'] aliases'].
      destruct (lvn' names' values' aliases' s2) as [[[s2' names''] values''] aliases''] eqn:E2.
      econstructor. 1: exact IHHexec.
      simpl. intros. fwd.
      specialize (H0 _ _ _ _ ltac:(eassumption) ltac:(assumption) ltac:(assumption)).
      specialize (H0 l' mc' names' values' aliases' ssa_hyps' ltac:(assumption)).
      rewrite E2 in H0. apply H0.
    - econstructor. do 2 eexists. eauto.
  Abort.
End LVN.

Definition example1 : stmt Z := SSeq (SSet 2 1) (SLoad access_size.word 3 2 0).

Check (ssa Z Z.ltb Z_strict_order).
Local Notation ssa_ := (ssa Z Z.ltb Z_strict_order).

Definition example1_ssa := fst (ssa_ example1).
Compute example1_ssa.

Local Notation lvn_ := (lvn Z Z.ltb Z_strict_order).
Compute (match example1_ssa with |SSeq a b => a |_ => SSkip end).
Compute (lvn_ example1_ssa).
