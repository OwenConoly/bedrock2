Require Import coqutil.Macros.subst coqutil.Macros.unique coqutil.Map.Interface coqutil.Word.Properties.
Require Import coqutil.Word.Bitwidth.
Require bedrock2.WeakestPrecondition.

Require Import Coq.Classes.Morphisms.

Section WeakestPrecondition.
  Context {width} {BW: Bitwidth width} {word: word.word width} {mem: map.map word Byte.byte}.
  Context {locals: map.map String.string word}.
  Context {env: map.map String.string (list String.string * list String.string * Syntax.cmd)}.
  Context {ext_spec: Semantics.ExtSpec}.

  Ltac ind_on X :=
    intros;
    (* Note: Comment below dates from when we were using a parameter record p *)
    (* Note: "before p" means actually "after p" when reading from top to bottom, because,
       as the manual points out, "before" and "after" are with respect to the direction of
       the move, and we're moving hypotheses upwards here.
       We need to make sure not to revert/clear p, because the other lemmas depend on it.
       If we still reverted/cleared p, we'd get errors like
       "Error: Proper_load depends on the variable p which is not declared in the context."
       when trying to use Proper_load, or, due to COQBUG https://github.com/coq/coq/issues/11487,
       we'd get a typechecking failure at Qed time. *)
    repeat match goal with x : ?T |- _ => first
       [ constr_eq T X; move x before ext_spec
       | constr_eq T X; move x before env
       | constr_eq T X; move x before locals
       | constr_eq T X; move x at top
       | revert x ] end;
    match goal with x : X |- _ => induction x end;
    intros.

  Local Hint Mode word.word - : typeclass_instances.

  (* we prove weakening lemmas for all WP definitions in a syntax-directed fashion,
   * moving from postcondition towards precondition one logical connective at a time. *)
  Global Instance Proper_literal : Proper (pointwise_relation _ ((pointwise_relation _ Basics.impl) ==> Basics.impl)) WeakestPrecondition.literal.
  Proof using. clear. cbv [WeakestPrecondition.literal]; cbv [Proper respectful pointwise_relation Basics.impl dlet.dlet]. eauto. Qed.

  Global Instance Proper_get : Proper (pointwise_relation _ (pointwise_relation _ ((pointwise_relation _ Basics.impl) ==> Basics.impl))) WeakestPrecondition.get.
  Proof using. clear. cbv [WeakestPrecondition.get]; cbv [Proper respectful pointwise_relation Basics.impl]; intros * ? (?&?&?); eauto. Qed.

  Global Instance Proper_load : Proper (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ ((pointwise_relation _ Basics.impl) ==> Basics.impl)))) WeakestPrecondition.load.
  Proof using. clear. cbv [WeakestPrecondition.load]; cbv [Proper respectful pointwise_relation Basics.impl]; intros * ? (?&?&?); eauto. Qed.

  Global Instance Proper_store : Proper (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ ((pointwise_relation _ Basics.impl) ==> Basics.impl))))) WeakestPrecondition.store.
  Proof using. clear. cbv [WeakestPrecondition.store]; cbv [Proper respectful pointwise_relation Basics.impl]; intros * ? (?&?&?); eauto. Qed.

  Global Instance Proper_expr : Proper (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ ((pointwise_relation _ (pointwise_relation _ Basics.impl) ==> Basics.impl)))))) WeakestPrecondition.expr.
  Proof using.
    clear.
    cbv [Proper respectful pointwise_relation Basics.impl]; ind_on Syntax.expr.expr;
      cbn in *; intuition (try typeclasses eauto with core).
    { eapply Proper_literal; eauto. cbv [pointwise_relation Basics.impl]. auto. }
    { eapply Proper_get; eauto. cbv [pointwise_relation Basics.impl]. auto. }
    { eapply IHa2; eauto; intuition idtac. cbv [WeakestPrecondition.pop_read] in *.
     repeat Tactics.destruct_one_match; auto. eapply Proper_load; eauto using Proper_load. cbv [pointwise_relation Basics.impl]. auto. }
    { eapply IHa2; eauto; intuition idtac. eapply Proper_load; eauto using Proper_load. cbv [pointwise_relation Basics.impl]. auto. }
    { eapply IHa2_1; eauto; intuition idtac. cbv [WeakestPrecondition.pop_branch] in *.
      repeat Tactics.destruct_one_match; eauto using Proper_load. }
  Qed.

  Global Instance Proper_list_map {A B} :
    Proper ((pointwise_relation _ (pointwise_relation _ Basics.impl ==> Basics.impl)) ==> pointwise_relation _ (pointwise_relation _ Basics.impl ==> Basics.impl)) (WeakestPrecondition.list_map (A:=A) (B:=B)).
  Proof using.
    clear.
    cbv [Proper respectful pointwise_relation Basics.impl]; ind_on (list A);
      cbn in *; intuition (try typeclasses eauto with core).
  Qed.
  
  Global Instance Proper_list_map' {A B T} :
    Proper ((pointwise_relation _ (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ Basics.impl) ==> Basics.impl)) ==> pointwise_relation _ (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ Basics.impl) ==> Basics.impl)))) (WeakestPrecondition.list_map' (A:=A) (B:=B) (T:=T)).
  Proof using.
    clear.
    cbv [Proper respectful pointwise_relation Basics.impl]; ind_on (list A);
      cbn in *; intuition (try typeclasses eauto with core).
  Qed.

  Context {word_ok : word.ok word} {mem_ok : map.ok mem}.
  Context {locals_ok : map.ok locals}.
  Context {env_ok : map.ok env}.
  Context {ext_spec_ok : Semantics.ext_spec.ok ext_spec}. Check @WeakestPrecondition.cmd.
  
  Global Instance Proper_cmd :
    Proper (
        (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ ((pointwise_relation _ (pointwise_relation _ Basics.impl)))) ==> Basics.impl))))) ==>
     pointwise_relation _ (
     pointwise_relation _ (
     pointwise_relation _ (
     pointwise_relation _ (
     pointwise_relation _ (
     (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ Basics.impl)))) ==>
     Basics.impl))))))) WeakestPrecondition.cmd.
  Proof using env_ok ext_spec_ok locals_ok mem_ok word_ok.
    cbv [Proper respectful pointwise_relation Basics.flip Basics.impl]; ind_on Syntax.cmd.cmd;
      cbn in *; cbv [dlet.dlet] in *; intuition eauto.
    (*intuition (try typeclasses eauto with core). this doesn't do anything?*)
    { destruct H1 as (?&?&?&?). eexists. eexists. split.
      1: eapply Proper_expr; eauto.
      1: cbv [pointwise_relation Basics.impl]; intuition eauto 2.
      auto. }
    { destruct H1 as (?&?&?&?). eexists. eexists. split.
      { eapply Proper_expr; eauto; cbv [pointwise_relation Basics.impl]; eauto. }
      { destruct H2 as (?&?&?&?). eexists. eexists. split.
        { eapply Proper_expr; eauto; cbv [pointwise_relation Basics.impl]; eauto. }
        { eapply Proper_store; eauto; cbv [pointwise_relation Basics.impl]; eauto. } } }
    { destruct H1 as (?&?&?&?). subst. eexists. split; [reflexivity|]. split; eauto.
      intros. eapply H2; [ | | eapply H4; eassumption].
      { intros. eauto. }
      { cbv beta. intros ? ? ? ? (?&?&?&?&?). eexists. eexists. split; eauto. } }
    { destruct H1 as (?&?&?&?&?). eexists. eexists. eexists.
      { eapply Proper_expr; eauto; cbv [pointwise_relation Basics.impl]. intros. eassumption. }
      { intuition eauto. } }
    { eapply H4; eauto. intros. intuition eauto. }

    { destruct H1 as (?&?&?&?&?&HH).
      eassumption || eexists.
      eassumption || eexists.
      eassumption || eexists.
      eassumption || eexists. { eassumption || eexists. }
      eassumption || eexists. { eassumption || eexists. }
      intros X Y Z T A W.
      specialize (HH X Y Z T A W).
      destruct HH as (?&?&?&?&?). eexists. eexists. eexists.
      1: eapply Proper_expr; eauto.
      1: cbv [pointwise_relation Basics.impl].
      all:intuition eauto 2.
      - eapply H2; eauto; cbn; intros.
        match goal with H:_ |- _ => destruct H as (?&?&?); solve[eauto] end.
      - intuition eauto. }
    { destruct H1 as (?&?&?&?). eexists. eexists. split.
      { eapply Proper_list_map'; eauto; try exact H4; cbv [respectful pointwise_relation Basics.impl]; intuition eauto 2.
        eapply Proper_expr; eauto. }
      { eapply H. 2: eauto.
        (* COQBUG (performance), measured in Coq 8.9:
           "firstorder eauto" works, but takes ~100s and increases memory usage by 1.8GB.
           On the other hand, the line below takes just 5ms *)
        cbv beta; intros ? ? ? ? (?&?&?); eauto. } }
    { destruct H1 as (?&?&?&?). eexists. eexists. split.
      { eassumption. }
      { destruct H2 as (mKeep & mGive & ? & ?).
        exists mKeep. exists mGive.
        split; [assumption|].
        eapply Semantics.ext_spec.weaken; [|solve[eassumption]].
        intros ? ? (?&?&?); eauto 10. } }
  Qed.

  Global Instance Proper_func :
    Proper (
        (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ ((pointwise_relation _ (pointwise_relation _ (pointwise_relation _ Basics.impl)))) ==> Basics.impl))))) ==>
     pointwise_relation _ (
     pointwise_relation _ (
     pointwise_relation _ (
     pointwise_relation _ (
     pointwise_relation _ (
     (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ Basics.impl)))) ==>
     Basics.impl))))))) WeakestPrecondition.func.
  Proof using word_ok mem_ok locals_ok ext_spec_ok env_ok.
    cbv [Proper respectful pointwise_relation Basics.flip Basics.impl  WeakestPrecondition.func]; intros.
    destruct a. destruct p.
    destruct H1; intuition idtac.
    eexists.
    split; [eauto|].
    eapply Proper_cmd;
      cbv [Proper respectful pointwise_relation Basics.flip Basics.impl  WeakestPrecondition.func];
      try solve [typeclasses eauto with core].
    intros.
    eapply Proper_list_map;
      cbv [Proper respectful pointwise_relation Basics.flip Basics.impl  WeakestPrecondition.func];
      try solve [typeclasses eauto with core].
    - intros.
      eapply Proper_get;
        cbv [Proper respectful pointwise_relation Basics.flip Basics.impl  WeakestPrecondition.func];
        eauto.
    - eauto.
  Qed.
  
  Global Instance Proper_call :
    Proper (
     (pointwise_relation _ (
     (pointwise_relation _ (
     pointwise_relation _ (
     pointwise_relation _ (
     pointwise_relation _ (
     pointwise_relation _ (
     (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ Basics.impl)))) ==>
     Basics.impl))))))))) WeakestPrecondition.call.
  Proof using word_ok mem_ok locals_ok ext_spec_ok env_ok.
      cbv [Proper respectful pointwise_relation Basics.impl]; ind_on (list (String.string * (list String.string * list String.string * Syntax.cmd.cmd)));
      cbn in *; intuition (try typeclasses eauto with core).
    destruct a.
    destruct (String.eqb s a1); debug eauto.
    
    eapply Proper_func;
      cbv [Proper respectful pointwise_relation Basics.flip Basics.impl  WeakestPrecondition.func];
      eauto.
  Qed.
  
  Global Instance Proper_program :
    Proper (
     pointwise_relation _ (
     pointwise_relation _ (
     pointwise_relation _ (
     pointwise_relation _ (
     pointwise_relation _ (
     pointwise_relation _ (
     (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ Basics.impl)))) ==>
     Basics.impl))))))) WeakestPrecondition.program.
  Proof using word_ok mem_ok locals_ok ext_spec_ok env_ok.
    cbv [Proper respectful pointwise_relation Basics.impl  WeakestPrecondition.program]; intros.
    eapply Proper_cmd;
    cbv [Proper respectful pointwise_relation Basics.flip Basics.impl  WeakestPrecondition.func];
    try solve [typeclasses eauto with core].
    intros.
    eapply Proper_call;
    cbv [Proper respectful pointwise_relation Basics.flip Basics.impl  WeakestPrecondition.func];
    solve [typeclasses eauto with core].
  Qed.

  Ltac step_t :=
    match goal with
    | |- forall _, _ => progress intros
    | H: exists _, _ |- _ => destruct H
    | H: and _ _ |- _ => destruct H
    | H: eq _ ?y |- _ => subst y
    | H: False |- _ => destruct H
    | _ => progress cbn in *
    | _ => progress cbv [dlet.dlet WeakestPrecondition.dexpr WeakestPrecondition.dexprs WeakestPrecondition.store] in *
    end.

  Ltac t := repeat step_t; eauto. 

  Lemma expr_sound: forall m l e mc a post (H : WeakestPrecondition.expr m l a e post),
    exists v mc' a', Semantics.eval_expr m l e mc a = Some (v, mc', a') /\ post a' v.
  Proof using word_ok.
    induction e; t.
    { destruct H. destruct H. eexists. eexists. rewrite H. eauto. }
    { eapply IHe in H; t.
      cbv [WeakestPrecondition.load Semantics.pop_read WeakestPrecondition.pop_read] in *; t.
      rewrite H.
      destruct x1; try solve [destruct H0]. destruct (andb _ _); try solve [destruct H0].
      destruct H0 as [v [H0p1 H0p2]].
      rewrite H0p1. eauto. }
    { eapply IHe in H; t. cbv [WeakestPrecondition.load] in H0; t. rewrite H. rewrite H0. eauto. }
    { eapply IHe1 in H; t. eapply IHe2 in H0; t. rewrite H, H0; eauto. }
    { eapply IHe1 in H; t.
      cbv [Semantics.pop_branch WeakestPrecondition.pop_branch] in *; t.
      rewrite H. destruct x1; try solve [destruct H0].
      destruct (Bool.eqb _ _); try solve [destruct H0]. Tactics.destruct_one_match.
      { eapply IHe3 in H0; t. }
      { eapply IHe2 in H0; t. } }
  Qed.

  Import ZArith coqutil.Tactics.Tactics.

  Lemma expr_complete: forall m l a e mc v mc' a',
    Semantics.eval_expr m l e mc a = Some (v, mc', a') ->
    WeakestPrecondition.dexpr m l a e v a'.
  Proof using word_ok.
    intros m l a e. generalize dependent a. induction e; cbn; intros.
    - inversion_clear H. cbv [WeakestPrecondition.literal]. t.
    - destruct_one_match_hyp. 2: discriminate. inversion H. subst r.
      eexists. eauto.
    - repeat (destruct_one_match_hyp; try discriminate; []).
      inversion H. subst r0 mc'. clear H.
      eapply Proper_expr.
      2: { eapply IHe. eassumption. }
      intros addr ? ?. t. unfold WeakestPrecondition.load.
      cbv [Semantics.pop_read WeakestPrecondition.pop_read] in *.
      destruct a1; try solve [congruence].
      destruct (andb _ _); try solve [congruence]. injection E1. eauto.
    - repeat (destruct_one_match_hyp; try discriminate; []).
      inversion H. subst r0 mc'. clear H.
      eapply Proper_expr.
      2: { eapply IHe. eassumption. }
      intros addr ? ?. t. unfold WeakestPrecondition.load. eauto.
    - repeat (destruct_one_match_hyp; try discriminate; []).
      inversion H. subst v mc'. clear H.
      eapply Proper_expr.
      2: { eapply IHe1. eassumption. }
      intros v1 ? ?. t.
      eapply Proper_expr.
      2: { eapply IHe2. eassumption. }
      intros v2 ? ?. t.
    - repeat (destruct_one_match_hyp; try discriminate; []).
      eapply Proper_expr.
      2: { eapply IHe1. eassumption. }
      intros vc ? ?. t.
      cbv [Semantics.pop_branch WeakestPrecondition.pop_branch] in *.
      destruct a0; try solve [congruence]. destruct (Bool.eqb _ _); try solve [congruence].
      injection E0 as E0. subst.
      destr (word.eqb r (word.of_Z 0)).
      + eapply IHe3. eassumption.
      + eapply IHe2. eassumption.
  Qed.

  Lemma sound_args : forall m l t args mc P,
      WeakestPrecondition.list_map' (WeakestPrecondition.expr m l) t args P ->
      exists x mc' t', Semantics.evaluate_call_args_log m l args mc t = Some (x, mc', t') /\ P t' x.
  Proof using word_ok.
    intros m l t args. generalize dependent t.
    induction args; cbn; repeat (subst; t).
    unfold Semantics.eval_expr in *.
    eapply expr_sound in H; t; rewrite H.
    eapply IHargs in H0. t; rewrite H0.
    eauto.
  Qed.

  Lemma sound_getmany l a P :
    WeakestPrecondition.list_map (WeakestPrecondition.get l) a P
    -> exists vs, map.getmany_of_list l a = Some vs /\ P vs.
  Proof using.
    cbv [map.getmany_of_list] in *.
    revert P l; induction a; cbn; repeat (subst; t).
    cbv [WeakestPrecondition.get] in H; t.
    epose proof (IHa _ l _); clear IHa; t.
    rewrite H. erewrite H1. eexists; split; eauto. exact H2.
    Unshelve.
    eapply Proper_list_map; try exact H0.
    all : cbv [respectful pointwise_relation Basics.impl WeakestPrecondition.get]; intros; cbv beta; t.
  Qed. Check WeakestPrecondition.cmd.

  Local Notation semantics_call := (fun e n t m a args post =>
    exists params rets fbody, map.get e n = Some (params, rets, fbody) /\
    exists lf, map.putmany_of_list_zip params args map.empty = Some lf /\
    forall mc', Semantics.exec e fbody t m lf mc' a (fun t' m' st1 mc'' a' =>
      exists retvs, map.getmany_of_list st1 rets = Some retvs /\
      post t' m' a' retvs)).

  Local Hint Constructors Semantics.exec : core.
  Lemma sound_cmd' e c t m l mc a post
        (H:WeakestPrecondition.cmd (semantics_call e) c t m l a post)
    : Semantics.exec e c t m l mc a (fun t' m' l' mc' a' => post t' m' l' a').
  Proof.
    ind_on Syntax.cmd; repeat (t; try match reverse goal with H : WeakestPrecondition.expr _ _ _ _ _ |- _ => eapply expr_sound in H end).
    { rewrite H. t. }
    { destruct (BinInt.Z.eq_dec (Interface.word.unsigned x) (BinNums.Z0)) as [Hb|Hb]; cycle 1.
      { specialize (H0 Hb). econstructor; t. apply Z.eqb_neq in Hb. rewrite Hb in H. eassumption. }
      { specialize (H1 Hb). eapply Semantics.exec.if_false; t. apply Z.eqb_eq in Hb. rewrite Hb in H. eassumption. } }
    { revert dependent l; revert dependent m; revert dependent t; revert dependent mc; revert dependent a. pattern x2.
      eapply (well_founded_ind H); t.
      pose proof (H1 _ _ _ _ _ ltac:(eassumption));
        repeat (t; try match goal with H : WeakestPrecondition.expr _ _ _ _ _ |- _ => eapply expr_sound in H end).
      { destruct (BinInt.Z.eq_dec (Interface.word.unsigned x4) (BinNums.Z0)) as [Hb|Hb].
        { specialize (H5 Hb). eapply Semantics.exec.while_false; t. apply Z.eqb_eq in Hb. rewrite Hb in H3. eassumption. }
        { specialize (H4 Hb). eapply Semantics.exec.while_true; t. 2: t. apply Z.eqb_neq in Hb. rewrite Hb in H3. eassumption. } } }
    { eapply sound_args in H; t. }
    { eapply sound_args in H0; t. }
  Qed.

  Section WithE.
    Context fs (E: env) (HE: List.Forall (fun '(k, v) => map.get E k = Some v) fs).
    Import coqutil.Tactics.Tactics.
    Lemma sound_call' n t m a args post
      (H : WeakestPrecondition.call fs n t m a args post)
      : semantics_call E n t m a args post.
    Proof.
      revert H; revert post args m t n a; induction HE; intros.
      { contradiction H. }
      destruct x as [n' ((X&Y)&Z)]; t.
      destr (String.eqb n' n); t.
      eexists X, Y, Z; split; [assumption|].
      eexists; eauto.
      eexists; eauto.
      intros.
      eapply sound_cmd'.
      eapply Proper_cmd; try eapply H0.
      all : cbv [respectful pointwise_relation Basics.impl]; intros; cbv beta.
      1: eapply IHf, Proper_call; eauto.
      2: eassumption.
      eauto using sound_getmany.
    Qed.

    Lemma sound_cmd'' c t m l mc a post
      (H : WeakestPrecondition.cmd (WeakestPrecondition.call fs) c t m l a post)
      : Semantics.exec E c t m l mc a (fun t' m' l' mc' a' => post t' m' l' a').
    Proof.
      eapply Proper_cmd in H; [ .. | reflexivity ].
      1: apply sound_cmd'; exact H.
      cbv [respectful pointwise_relation Basics.impl]; intros; cbv beta.
      eapply sound_call', Proper_call, H1.
      cbv [respectful pointwise_relation Basics.impl]; eauto.
    Qed.
  End WithE.

  Lemma sound_cmd fs c t m l mc a post
    (Hnd : List.NoDup (List.map fst fs))
    (H : WeakestPrecondition.cmd (WeakestPrecondition.call fs) c t m l a post)
    : Semantics.exec (map.of_list fs) c t m l mc a (fun t' m' l' mc' a' => post t' m' l' a').
  Proof.
    eapply sound_cmd'';
      try eapply Properties.map.all_gets_from_map_of_NoDup_list; eauto.
  Qed.

  (** Ad-hoc lemmas here? *)

  Import bedrock2.Syntax bedrock2.Semantics bedrock2.WeakestPrecondition.
  Lemma interact_nomem call action binds arges t m l a post
        args f (Hargs : dexprs m l a arges args (cons_IO (map.empty, binds, args) f))
        (Hext : ext_spec t map.empty binds args (fun mReceive (rets : list word) =>
           mReceive = map.empty /\
           exists l0 : locals, map.putmany_of_list_zip action rets l = Some l0 /\
           post (cons ((map.empty, binds, args), (map.empty, rets)) t) m l0 (f (map.empty, rets))))
    : WeakestPrecondition.cmd call (cmd.interact action binds arges) t m l a post.
  Proof using word_ok mem_ok ext_spec_ok.
    exists m.
    exists map.empty.
    split; [eapply Properties.map.split_empty_r; exact eq_refl|].
    exists args. exists f. split; [exact Hargs|].
    eapply ext_spec.weaken; [|eapply Hext]; intros ? ? [? [? []]]. subst a0; subst.
    eexists; split; [eassumption|].
    intros. eapply Properties.map.split_empty_r in H. subst. assumption.
  Qed.

  Lemma intersect_expr: forall m l t e (post1 post2: abstract_trace -> word -> Prop),
      WeakestPrecondition.expr m l t e post1 ->
      WeakestPrecondition.expr m l t e post2 ->
      WeakestPrecondition.expr m l t e (fun t v => post1 t v /\ post2 t v).
  Proof using word_ok.
    intros m l t e. generalize dependent t.
    induction e; cbn; unfold literal, dlet.dlet, WeakestPrecondition.get; intros.
    - eauto.
    - decompose [and ex] H. decompose [and ex] H0. assert (x0 = x1) by congruence. subst. eauto.
    - eapply Proper_expr.
      2: eapply IHe.
      2: eapply H.
      2: eapply H0.
      unfold Morphisms.pointwise_relation, Basics.impl.
      unfold load. intros. cbv [pop_read] in *.
      destruct a0; try solve [destruct H1; congruence].
      destruct (andb _ _); try solve [destruct H1; congruence].
      decompose [and ex] H1. assert (x0 = x) by congruence. subst. eauto.
    - eapply Proper_expr.
      2: eapply IHe.
      2: eapply H.
      2: eapply H0.
      unfold Morphisms.pointwise_relation, Basics.impl.
      unfold load. intros. decompose [and ex] H1. assert (x0 = x) by congruence. subst. eauto.
    - eapply Proper_expr.
      2: eapply IHe1.
      2: eapply H.
      2: eapply H0.
      unfold Morphisms.pointwise_relation, Basics.impl.
      unfold load. intros. decompose [and ex] H1.
      eapply IHe2; eassumption.
    - eapply Proper_expr.
      2: eapply IHe1.
      2: eapply H.
      2: eapply H0.
      unfold Morphisms.pointwise_relation, Basics.impl.
      intros ? ? [? ?]. cbv [pop_branch] in *.
      destruct a; try solve [destruct H1; congruence].
      destruct (Bool.eqb _ _); try solve [destruct H1; congruence].
      Tactics.destruct_one_match; eauto using Proper_expr.
  Qed.

  Lemma dexpr_expr (m : mem) l a e P
    (H : WeakestPrecondition.expr m l a e P)
    : exists v a', WeakestPrecondition.dexpr m l a e v a' /\ P a' v.
  Proof using word_ok.
    generalize dependent a.
    revert dependent P; induction e; cbn.
    { cbv [WeakestPrecondition.literal dlet.dlet]; cbn; eauto. }
    { cbv [WeakestPrecondition.get]. intros ? ? [? [? ?] ]. eexists. eexists. eauto. }
    { intros P a' H. apply IHe in H. destruct H as (?&?&?&?). cbv [pop_read] in *.
      destruct x0; try solve [destruct H0; congruence].
      destruct (andb _ _) eqn:E; try solve [destruct H0; congruence].
      cbv [WeakestPrecondition.dexpr load] in *.
      destruct H0 as [v [H0p1 H0p2]].
      eexists. eexists. split; [|eassumption].
      eapply Proper_expr; [|eauto].
      intros ? ? [? ?]; subst.
      rewrite E.
      eexists; eauto. }
    { intros P a' H; case (IHe _ _ H) as (?&?&?&?&?&?); clear IHe H.
      cbv [WeakestPrecondition.dexpr] in *.
      eexists. eexists. split; [|eassumption].
      eapply Proper_expr; [|eauto].
      intros ? ? [? ?]; subst.
      eexists; eauto. }
    { intros P a H.
      case (IHe1 _ _ H) as (?&?&?&H'); case (IHe2 _ _ H') as (?&?&?&?);
      clear IHe1 IHe2 H H'.
      cbv [WeakestPrecondition.dexpr] in *.
      eexists. eexists. split; [|eassumption].
      eapply Proper_expr; [|eauto]; intros ? ? [].
      eapply Proper_expr; subst; [|eauto]; intros ? ? [].
      subst. split; reflexivity.
    }
    { intros P t H.
      case (IHe1 _ _ H) as (?&?&?&H').
      destruct x0; try solve [destruct H']. cbv [pop_branch] in *.
      destruct (Bool.eqb _ _) eqn:E; try solve [destruct H'; congruence].
      Tactics.destruct_one_match_hyp.
      { case (IHe3 _ _ H') as (?&?&?&?).
        clear IHe1 IHe2 H H'.
        cbv [WeakestPrecondition.dexpr] in *.
        eexists. eexists. split; [|eassumption].
        eapply Proper_expr; [|eauto]; intros ? ? [].
        subst. rewrite word.eqb_eq by reflexivity. rewrite E. assumption. }
      { case (IHe2 _ _ H') as (?&?&?&?).
        clear IHe1 IHe3 H H'.
        cbv [WeakestPrecondition.dexpr] in *.
        eexists. eexists. split; [|eassumption].
        eapply Proper_expr; [|eauto]; intros ? ? [].
        subst. rewrite word.eqb_ne by assumption. rewrite E. assumption. } }
  Qed.
End WeakestPrecondition.
