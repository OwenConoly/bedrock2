Require Import compiler.FlatImp.
Require Import Coq.Lists.List. Import ListNotations.
Require Import bedrock2.Syntax.
Require Import bedrock2.ProgramLogic.
Require Import coqutil.Tactics.fwd.
Require Import String.
Require Import coqutil.Map.MapEauto.
Open Scope Z_scope.
Require Import coqutil.Datatypes.PropSet.
Require Import coqutil.Datatypes.ListSet.
Local Notation var := String.string (only parsing).
Require Import compiler.util.Common.
Require Import bedrock2.MetricLogging.
Require Import coqutil.Tactics.fwd.
(*  below only for of_list_list_diff *)
Require Import compiler.DeadCodeElimDef.

Section WithArguments1.
  Context {width: Z}.
  Context {BW: Bitwidth.Bitwidth width }.
  Context {word : word width } { word_ok : word.ok word }.
  Context {env: map.map string (list var * list var * stmt var) } { env_ok : map.ok env }.
  Context {mem: map.map word (Init.Byte.byte : Type) } {mem_ok : map.ok mem } .
  Context {locals: map.map string word } {locals_ok : map.ok locals }.
  Context {ext_spec : Semantics.ExtSpec } {ext_spec_ok: Semantics.ext_spec.ok ext_spec } .

  Section MapEautoStuff.
    Local Set Default Proof Using "All".
    Import Interface.map.
    Context {var: Type}. (* variable name (key) *)
    Context {var_eqb: var -> var -> bool}.
    Context {var_eqb_spec: EqDecider var_eqb}.
    Context {val: Type}. (* value *)
    
    Context {stateMap: map.map var val}.
    Context {stateMapSpecs: map.ok stateMap}.
    Notation state := (@map.rep var val).
    Local Hint Mode map.map - - : typeclass_instances.

    Ltac t := map_solver stateMapSpecs.

    Lemma agree_on_not_in:
      forall keySet (m: stateMap) x,
        List.existsb (var_eqb x) keySet = false ->
        forall y,
          map.agree_on (PropSet.of_list keySet) (map.put m x y) m.
    Proof.
      intros.
      unfold map.agree_on.
      intros.
      rewrite map.get_put_dec.
      destr (var_eqb x k).
      - unfold elem_of in H0. apply (*PropSet.*)existsb_of_list in H0. exfalso. rewrite H in H0. discriminate.
      - reflexivity.
    Qed.

    Lemma agree_on_put_not_in :
      forall x l (m1 m2: stateMap),
        map.agree_on (PropSet.of_list l) m1 m2
        -> List.existsb (var_eqb x) l = false
        -> forall v,
            map.agree_on (PropSet.of_list l) (map.put m1 x v) m2.
    Proof.
      intros.
      unfold map.agree_on.
      intros.
      erewrite agree_on_not_in.
      - rewrite H.
        + reflexivity.
        + assumption.
      - eassumption.
      - eassumption.
    Qed.

    Lemma agree_on_subset:
      forall ks ks' (m1 m2: stateMap),
        subset ks' ks ->
        map.agree_on ks m1 m2 ->
        map.agree_on ks' m1 m2.
    Proof. t. Qed.

    Lemma agree_on_diff_put:
      forall a r s (mH mL: stateMap),
        map.agree_on (diff (PropSet.of_list s) (singleton_set a)) mH mL ->
        map.agree_on (PropSet.of_list s) (map.put mH a r) (map.put mL a r).
    Proof.
      intros. t.
    Qed.

    Lemma agree_on_comm :
      forall ks (m1 m2: stateMap),
        map.agree_on ks m1 m2 ->
        map.agree_on ks m2 m1.
    Proof. t. Qed.
    
    Lemma agree_on_union:
      forall s0 s1 (m0 m1: stateMap),
        map.agree_on (union s0 s1) m0 m1
        <-> map.agree_on s0 m0 m1 /\ map.agree_on s1 m0 m1.
    Proof.
      intros. unfold iff; split; intros; t.
    Qed.

    Lemma agree_on_put:
      forall a r s (mH mL: stateMap) mH' mL',
        map.agree_on s mH mL ->
        map.put mH a r = mH' ->
        map.put mL a r = mL' ->
        map.agree_on (union s (singleton_set a)) mH' mL'.
    Proof.
      intros.
      rewrite <- H0, <- H1. 
      t.
    Qed.

    Lemma agree_on_putmany_of_list_zip:
      forall lk0 lv s (mH mL: stateMap) mH' mL',
        map.agree_on s mH mL ->
        map.putmany_of_list_zip lk0 lv mH = Some mH' ->
        map.putmany_of_list_zip lk0 lv mL = Some mL' ->
        map.agree_on (union s (PropSet.of_list lk0)) mH' mL'.
    Proof.
      induction lk0.
      - intros. simpl in *.
        destr lv; [ | discriminate ].
        inversion H0. inversion H1.
        rewrite <- H3, <- H4.
        eapply agree_on_union.
        split.
        + t.
        + unfold agree_on, PropSet.of_list, elem_of.
          intros.
          exfalso; eapply List.in_nil.
          eassumption.
      - intros.
        destr lv; [ discriminate | ].
        simpl in *.
        cut (map.agree_on (union s (singleton_set a))
               (map.put mH a v) (map.put mL a v)).
        + intros.
          eapply IHlk0 in H2.
          2-3: eassumption.
          eapply agree_on_subset.
          2: eassumption.
          set_solver_generic var.
        + eapply agree_on_put.
          * eassumption.
          * reflexivity.
          * reflexivity.
    Qed.

    Lemma agree_on_cons:
      forall (k: var) ks (m1 m2: stateMap),
        map.agree_on (PropSet.of_list (k :: ks)) m1 m2 ->
        map.agree_on (PropSet.of_list ks) m1 m2 /\
          map.get m1 k = map.get m2 k.
    Proof.
      intros.
      unfold map.agree_on, PropSet.of_list, PropSet.elem_of in *.
      split.
      - intros. eauto using List.in_cons.
      - intros. eauto using List.in_eq.
    Qed.
    
    Lemma agree_on_getmany:
      forall ks (m1 m2: stateMap),
        map.agree_on (PropSet.of_list ks) m1 m2 ->
        map.getmany_of_list m1 ks =
          map.getmany_of_list m2 ks.
    Proof.
      intros.
      induction ks.
      - simpl. reflexivity.
      - simpl.
        eapply agree_on_cons in H.
        destr H.
        eapply IHks in H.
        unfold getmany_of_list in *.
        simpl.
        rewrite H, H0.
        reflexivity.
    Qed.

    Lemma agree_on_refl: forall k (m: stateMap),
        map.agree_on k m m.
    Proof. t. Qed.

    Lemma agree_on_find:
      forall s l (m1 m2: stateMap),
        map.agree_on (PropSet.of_list (if (List.find (var_eqb s) l)
                                       then l
                                       else s :: l)) m1 m2
        -> map.agree_on (PropSet.of_list l) m1 m2 /\ map.get m1 s = map.get m2 s.
    Proof.
      intros.
      destr (List.find (var_eqb s) l).
      - split.
        + eassumption. 
        + eapply List.find_some in E.
          unfold map.agree_on, elem_of, singleton_set in *.
          intros. destr E.
          unfold PropSet.of_list in H.
          destr (var_eqb s v).
          2: { exfalso; inversion H1. }
          eauto.
      - eauto using agree_on_cons. 
    Qed.
  End MapEautoStuff.
    
  Lemma agree_on_put_existsb_false:
    forall used_after x (l: locals) lL,
      map.agree_on (diff (of_list used_after) (singleton_set x)) l lL
      -> existsb (eqb x) used_after = false
      -> forall v, map.agree_on (of_list used_after) (map.put l x v) lL.
  Proof.
    intros. eapply agree_on_put_not_in; try eassumption.
    eapply agree_on_subset.
    2: { eapply H. }
    - unfold subset, diff, singleton_set, elem_of.
      intros.
      propositional idtac.
      eapply existsb_of_list in H1. rewrite H1 in H0.
      discriminate. 
  Qed.

   Ltac subset_union_solve :=
     match goal  with
     | |- subset (union _ _) _  => eapply subset_union_l; subset_union_solve
     | |- subset _ (union (union _ _) (union _ _)) => idtac (* not planning to make sure this case is handled safely, so not handling it at all *)
     | |- subset (of_list ?x) (union (of_list ?y) (diff (of_list ?x) (of_list ?y))) =>
         try solve [ eapply subset_trans; [ | eapply union_comm ]; subset_union_solve ]
     | |- subset (of_list ?x) (union (diff (of_list ?x) (of_list ?y)) (of_list ?y)) => try solve [ eapply subset_trans; [ | eapply sameset_union_diff_of_list; eapply String.eqb_spec ]; subset_union_solve ]
     | |- subset _ (union (union ?x1 ?x2) ?y) =>
     (* try x1 \/ x2 *)
         try solve [ eapply subset_union_rl; subset_union_solve ];
     (* try x1 \/ y  *)
         try solve [ eapply subset_trans; [ | eapply subset_union_l; [ eapply subset_union_rl; eapply subset_union_rl; eapply subset_refl |  eapply subset_union_rr; eapply subset_refl ]];  subset_union_solve ];
     (* try x2 \/ y *)
         try solve [ eapply subset_trans; [ | eapply subset_union_l; [ eapply subset_union_rl; eapply subset_union_rr; eapply subset_refl |  eapply subset_union_rr; eapply subset_refl ]];  subset_union_solve ]
     | |- subset _ (union _ _)  =>
         try solve [ eapply subset_union_rl; subset_union_solve ]; try solve [ eapply subset_union_rr; subset_union_solve ]
     | |- subset ?x ?x => solve [ eapply subset_refl ]
     | |- _ => idtac
    end.

   Ltac agree_on_solve :=
     match goal with
    | H: map.agree_on (diff (of_list ?x) (singleton_set ?y)) ?l ?lL,
        H1: existsb (eqb ?y) ?x = false
      |- map.agree_on (of_list ?x) (map.put ?l ?y _) ?lL =>
        eapply agree_on_put_existsb_false; solve [eauto]
    | H: map.agree_on ?s ?x ?y |-
        map.agree_on _ ?x ?y =>
        eapply agree_on_subset with (ks := s);
        [ idtac | eapply H ]; subset_union_solve
    | H: map.agree_on ?s ?x ?y |-
        map.agree_on _ ?y ?x =>
        eapply agree_on_comm; agree_on_solve 
    | H: map.agree_on ?s ?mH ?mL,
        H1: map.putmany_of_list_zip ?lk ?lv ?mH = Some ?mH',
          H2: map.putmany_of_list_zip ?lk ?lv ?mL = Some ?mL'
      |- map.agree_on _ ?mH' ?mL' =>
        eapply agree_on_subset;
        [ idtac
        | eapply agree_on_putmany_of_list_zip;
          [ eapply H | eapply H1 | eapply H2 ]
        ]
    | H: map.agree_on (diff (of_list ?x) (singleton_set ?y)) ?l ?lL |-
        map.agree_on (of_list ?x) (map.put ?l ?y ?v) (map.put ?lL ?y ?v)
      => eapply agree_on_diff_put; eapply H
    | _ => idtac
    end.

  Ltac listset_to_set :=
    match goal with
    | H: context[of_list (ListSet.list_union _ _ _)] |- _ => rewrite ListSet.of_list_list_union in H
    | H: context[of_list (ListSet.list_diff _ _ _)] |- _ =>
        rewrite of_list_list_diff in H;
        try match goal with
          | |- EqDecider String.eqb => eapply String.eqb_spec
          end
    | H: context[of_list (List.removeb _ _ _)] |- _ =>
        rewrite ListSet.of_list_removeb in H
    | |- context[of_list (ListSet.list_union _ _ _)]  => rewrite ListSet.of_list_list_union
    | |- context[of_list (ListSet.list_diff _ _ _)]  =>
        rewrite of_list_list_diff;
        try match goal with
          | |- EqDecider String.eqb => eapply String.eqb_spec
          end
    | |- context[of_list (List.removeb _ _ _)] =>
        rewrite ListSet.of_list_removeb
    end.

  Print compile_post.

  Lemma dce_correct_aux :
    forall eH eL,
      dce_functions eH = Success eL ->
      forall sH kH t m mcH lH postH,
        exec eH sH kH t m lH mcH postH ->
        forall used_after kL lL mcL,
          map.agree_on (of_list (live sH used_after)) lH lL ->
          exec eL (dce sH used_after) kL t m lL mcL (compile_post eH sH kH kL used_after postH).
  Proof.
    induction 2;
      match goal with
      | |- context[SLoop] => idtac
      | |- _ => simpl in *
      end.
    - intros.
      eapply @exec.interact; try solve [eassumption].
      + erewrite agree_on_getmany.
        * eapply H1.
        * repeat listset_to_set. agree_on_solve.
      + intros.
        eapply H3 in H5.
        fwd.
        let Heq := fresh in
        pose proof H5p0 as Heq;
        eapply map.putmany_of_list_zip_sameLength, map.sameLength_putmany_of_list in Heq.
        fwd.
        eexists.
        split.
        * eapply H5.
        * intros.
          unfold compile_post.
          do 3 eexists. exists l'. eexists. ssplit.
          -- agree_on_solve. repeat listset_to_set.
             subset_union_solve.
          -- eauto.
          -- trace_alignment.
          -- trace_alignment.
          -- intros. simpl. rewrite fix_step. reflexivity.
    - intros.
      eapply @exec.call; try solve [ eassumption ].
      + unfold dce_functions, dce_function  in *.
        eapply map.try_map_values_fw in H.
        2: { eapply H0. }
        fwd. eassumption.
      + erewrite agree_on_getmany.
        * eapply H1.
        * listset_to_set. agree_on_solve. 
      + eapply IHexec.
        eapply agree_on_refl.
      + intros.
        unfold compile_post in *.
        fwd. eapply H4 in H6p1. fwd.
        let Heq := fresh in
        pose proof H6p1p1 as Heq;
        eapply map.putmany_of_list_zip_sameLength,  map.sameLength_putmany_of_list in H6p1p1. fwd.
        exists retvs. eexists. repeat split.
        * erewrite agree_on_getmany.
          -- eapply H6p1p0.
          -- listset_to_set. agree_on_solve.
        * eapply H6p1p1.
        * do 5 eexists. ssplit; try eassumption; trace_alignment.
          -- agree_on_solve. repeat listset_to_set. subset_union_solve.
          -- intros. rewrite fix_step. simpl.
             repeat rewrite rev_app_distr. repeat rewrite <- app_assoc. simpl.
             rewrite H0. rewrite H6p4. reflexivity.
             
    - intros.
      eapply agree_on_find in H3; fwd. 
      destr (existsb (eqb x) used_after); fwd.
      + eapply @exec.load.
        * rewrite <- H3p1. eassumption. 
        * eauto.
        * unfold compile_post.
          do 3 eexists. exists (map.put l x v); eexists; ssplit; try eassumption; trace_alignment.
          -- repeat listset_to_set. agree_on_solve.
          -- intros. simpl. rewrite fix_step. simpl. rewrite E. reflexivity.
      + eapply @exec.skip.
        * unfold compile_post.
          do 3 eexists. exists (map.put l x v); eexists; ssplit; try eassumption; trace_alignment.
          -- repeat listset_to_set. agree_on_solve.
          -- intros. simpl. rewrite fix_step. simpl. rewrite E. reflexivity.
    - intros. repeat listset_to_set.
      eapply agree_on_union in H4; fwd.
      all: try solve [ eauto using String.eqb_spec ].
      eapply @exec.store.
      + erewrite <- H4p0; eauto.
        unfold elem_of; destr (a =? v)%string; eapply in_eq.
      + erewrite <- H4p0; eauto.
        unfold elem_of; destr (a =? v)%string; [ eapply in_eq | eapply in_cons, in_eq ].
      + eassumption.
      + unfold compile_post. do 3 eexists.
        exists l; eexists; ssplit; try eassumption; trace_alignment.
        intros. rewrite fix_step. reflexivity.
    - intros.
      eapply agree_on_find in H4; fwd.
      destr (existsb (eqb x) used_after); fwd.
      + eapply @exec.inlinetable; eauto.
        * rewrite <- H4p1. eassumption. 
        * unfold compile_post; do 5 eexists; ssplit; try eassumption; trace_alignment.
          -- repeat listset_to_set; agree_on_solve.
          -- intros. rewrite fix_step. simpl. rewrite E. reflexivity.
      + eapply @exec.skip; eauto.
        unfold compile_post.
        do 5 eexists; ssplit; try eassumption; trace_alignment.
        -- repeat listset_to_set; agree_on_solve.
        -- intros. rewrite fix_step. simpl. rewrite E. reflexivity.
    - intros.
      repeat listset_to_set.
      eapply @exec.stackalloc.
      * eassumption.
      * intros. eapply H2 with (used_after := used_after) (lL :=  (map.put lL x a)) in H4.
        2: eapply H5.
        2: { agree_on_solve. }
        eapply @exec.weaken.
        -- eapply H4.
        --  unfold compile_post. intros. fwd. exists mSmall'. exists mStack'. split.
            ++ eassumption.
            ++ split.
               ** eassumption.
               ** do 5 eexists; ssplit; try eassumption; trace_alignment.
                  intros. rewrite rev_app_distr. rewrite <- app_assoc.
                  rewrite fix_step. simpl. rewrite H6p4. rewrite rev_app_distr.
                  reflexivity.
    - intros. destr (existsb (eqb x) used_after).
      + eapply @exec.lit.
        unfold compile_post.
        repeat listset_to_set.
        do 5 eexists; ssplit; try eassumption; trace_alignment.
        -- agree_on_solve.
        -- intros. rewrite fix_step. reflexivity.
      + eapply @exec.skip.
        unfold compile_post.
        repeat listset_to_set.
        do 5 eexists; ssplit; try eassumption; trace_alignment.
        -- agree_on_solve.
        -- intros. rewrite fix_step. reflexivity.
    - destr z.
      + intros. repeat listset_to_set.
        eapply agree_on_union in H3; try solve [ eauto using String.eqb_spec ].
        fwd.
        destr (existsb (eqb x) used_after).
        * eapply @exec.op.
          -- rewrite <- H3p0; [ eassumption | ].
             unfold elem_of; destr ((y =? v)%string).
             ++ eapply in_eq.
             ++ eapply in_eq.
          -- unfold exec.lookup_op_locals; simpl.
             rewrite <- H3p0; [ eassumption | ].
             unfold elem_of; destr ((y =? v)%string).
             ++ eapply in_eq.
             ++ eapply in_cons, in_eq.
          -- unfold compile_post.
             do 5 eexists; ssplit; try eassumption; trace_alignment.
             ++ agree_on_solve.
             ++ intros. rewrite fix_step. simpl. rewrite E. rewrite app_nil_r.
                destruct op; reflexivity.
        * eapply @exec.skip.
          unfold compile_post.
          do 5 eexists; ssplit; try eassumption; trace_alignment.
          -- agree_on_solve.
          -- intros. rewrite fix_step. simpl. rewrite E. rewrite app_nil_r.
             destruct op; reflexivity.
      + intros.
        eapply agree_on_find in H3; fwd. 
        destr (existsb (eqb x) used_after).
        * eapply @exec.op.
          -- rewrite <- H3p1. eassumption. 
          -- simpl. constructor.
          -- unfold compile_post. simpl in *. inversion H1. fwd.
             do 5 eexists; ssplit; try eassumption; trace_alignment.
             ++ repeat listset_to_set. agree_on_solve.
             ++ intros. rewrite fix_step. simpl. rewrite E. rewrite app_nil_r. 
                destruct op; reflexivity.
        * eapply @exec.skip. unfold compile_post.
          do 5 eexists; ssplit; try eassumption; trace_alignment.
          -- repeat listset_to_set. agree_on_solve.
          -- intros. rewrite app_nil_r. rewrite fix_step. simpl. rewrite E.
             destruct op; reflexivity.
    - intros.
      eapply agree_on_find in H2; fwd.
      repeat listset_to_set.
      destr (existsb (eqb x) used_after).
      { eapply @exec.set.
        - rewrite <- H2p1; eassumption. 
        - unfold compile_post. do 5 eexists; ssplit; try eassumption; trace_alignment.
          + agree_on_solve.
          + intros. rewrite fix_step. reflexivity.
      }
      { eapply @exec.skip.
        - unfold compile_post. do 5 eexists; ssplit; try eassumption; trace_alignment.
          + agree_on_solve.
          + intros. rewrite fix_step. reflexivity.
      }
    - intros.
      repeat listset_to_set.
      eapply agree_on_union in H2; fwd.
      eapply agree_on_union in H2p0; fwd.
      eapply @exec.if_true.
      + erewrite agree_on_eval_bcond; [ eassumption | ].
        pose agree_on_comm; eauto.
      + eapply exec.weaken; [eauto|]. intros. unfold compile_post in *.
        fwd. do 5 eexists; ssplit; try eassumption; trace_alignment.
        intros. repeat rewrite rev_app_distr. rewrite <- app_assoc. rewrite fix_step.
        simpl. rewrite H2p5. reflexivity.
    - intros.
      repeat listset_to_set.
      eapply agree_on_union in H2; fwd.
      eapply agree_on_union in H2p0; fwd.
      eapply @exec.if_false.
      + erewrite agree_on_eval_bcond; [ eassumption | ].
        pose agree_on_comm; eauto.
      + eapply exec.weaken; [eauto|]. intros. unfold compile_post in *.
        fwd. do 5 eexists; ssplit; try eassumption; trace_alignment.
        intros. repeat rewrite rev_app_distr. rewrite <- app_assoc. rewrite fix_step.
        simpl. rewrite H2p5. reflexivity.
    - intros.
      cbn - [live].
      rename IHexec into IH1.
      rename H6 into IH12.
      rename H4 into IH2.
      cbn - [live] in IH12.
      eapply @exec.loop_cps.
      eapply exec.weaken.
      { eapply IH1.
        eapply agree_on_subset.
        - let Heq := fresh in
          specialize (live_while body1 cond body2 used_after) as Heq; cbn zeta in Heq.
          eapply H4.
        - eapply H7.
      }
      Check exec.loop.
      intros.
      assert (eval_bcond l' cond <> None).
      { intros.
        unfold compile_post in *.
        fwd.
        eapply H1 in H4p1.
        erewrite agree_on_eval_bcond; [ eassumption | ].
        eapply agree_on_comm.
        repeat listset_to_set. Check agree_on_union.
        apply agree_on_union in H4p0.
        fwd.
        eapply agree_on_subset; [ | eapply H4p0p1 ].
        subset_union_solve.
      }
      destruct (eval_bcond l' cond) eqn:E; try congruence. exists b.
      split; [reflexivity|]. split.
      { intros.
        unfold compile_post in *.
        fwd.
        eapply H2 in H4p1.
        - do 3 eexists.
          exists lH'.
          eexists.
          ssplit; try eassumption; trace_alignment.
          + repeat listset_to_set.
            eapply agree_on_subset; [ | eapply H4p0 ].
            subset_union_solve.
          + intros. repeat rewrite app_nil_r. rewrite fix_step. simpl.
            rewrite <- app_assoc. rewrite H4p4. rewrite List.skipn_app_r by reflexivity.
            reflexivity.
        - subst. erewrite agree_on_eval_bcond; [ eassumption | ].
          repeat listset_to_set.
          eapply agree_on_subset; [ | eapply H4p0 ].
          subset_union_solve.
      }
      { Print exec.loop.
        intros.
        unfold compile_post in *.
        fwd.
        eapply exec.weaken.
        { eapply IH2.
          - eapply H4p1.
          - subst. erewrite agree_on_eval_bcond; [ eassumption | ].
            repeat listset_to_set.
            eapply agree_on_subset; [ | eapply H4p0 ].
            subset_union_solve.
          - repeat listset_to_set.
            eapply agree_on_subset; [ | eapply H4p0 ].
            subset_union_solve.
        }
        cbv beta. intros. fwd.
        eapply exec.weaken.
        { eapply IH12.
          - eapply H4p3.
          - eapply H4p2. }
        cbv beta. intros. fwd. do 5 eexists. ssplit; try eapply H4p6; trace_alignment.
        1: assumption.
        intros. repeat rewrite app_nil_r. repeat rewrite rev_app_distr. cbn [rev].
        rewrite fix_step. cbn [dtransform_stmt_trace_body]. repeat rewrite <- app_assoc.
        rewrite H4p4. rewrite List.skipn_app_r by reflexivity.
        cbn [List.app RecurseWithFun.Let_In_pf_nd]. rewrite H4p7.
        rewrite List.skipn_app_r by reflexivity. simpl. rewrite H4p10. reflexivity. }
    - intros.
      eapply @exec.seq.
      + eapply IHexec. eassumption.
      + unfold compile_post. intros. fwd.
        eapply @exec.weaken.
        * eapply H2.
          -- eassumption.
          -- eassumption.
        * unfold compile_post. intros. fwd.
          do 5 eexists; ssplit; try eassumption; trace_alignment.
          intros. repeat rewrite app_nil_r. repeat rewrite rev_app_distr.
          repeat rewrite <- app_assoc. rewrite fix_step. simpl. rewrite H4p4.
          rewrite List.skipn_app_r by reflexivity. rewrite H4p7. reflexivity.
    - intros.
      eapply @exec.skip.
      unfold compile_post. do 5 eexists; ssplit; try eassumption; trace_alignment.
      intros. rewrite fix_step. reflexivity.
  Qed.
End WithArguments1.
