Require Import bedrock2.LeakageSemantics.
Require Import compiler.FlatImp.
Require Import Coq.Lists.List. Import ListNotations.
Require Import bedrock2.Syntax.
Require Import coqutil.Tactics.fwd.
Require Import String.
Require Import coqutil.Map.MapEauto.
Open Scope Z_scope.
Require Import coqutil.Datatypes.PropSet.
Require Import coqutil.Datatypes.ListSet.
Local Notation var := String.string (only parsing).
Require Import compiler.util.Common.
Require Import bedrock2.MetricLogging.
Require Import bedrock2.MetricCosts.
(*  below only for of_list_list_diff *)
Require Import compiler.DeadCodeElimDef.

Local Notation exec e pick_sp := (@exec _ _ _ _ _ _ _ _ PreSpill isRegStr pick_sp e).

Section WithArguments1.
  Context {width: Z}.
  Context {BW: Bitwidth.Bitwidth width}.
  Context {word : word width} {word_ok : word.ok word}.
  Context {env: map.map string (list var * list var * stmt var)} {env_ok : map.ok env}.
  Context {mem: map.map word (Init.Byte.byte : Type) } {mem_ok : map.ok mem} .
  Context {locals: map.map string word} {locals_ok: map.ok locals}.
  Context {ext_spec: LeakageSemantics.ExtSpec} {ext_spec_ok: LeakageSemantics.ext_spec.ok ext_spec}.
  
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

  Ltac solve_compile_post :=
    do 5 eexists; ssplit;
    [eauto | repeat listset_to_set; agree_on_solve | scost_hammer | align_trace | align_trace |
      intros; rewrite dfix_step; simpl_rev; cbv beta; try reflexivity ].
                                                             
  Lemma dce_correct_aux :
    forall eH eL pick_spL,
      dce_functions eH = Success eL ->
      forall pick_spH sH kH t m mcH lH postH,
        exec pick_spH eH sH kH t m lH mcH postH ->
        forall f used_after kL lL mcL,
          map.agree_on (of_list (live sH used_after)) lH lL ->
          (forall k, pick_spH (k ++ kH) = pick_spL (rev kL ++ stmt_leakage eH (rev k, sH, used_after, f k))) ->
          exec (fun k => pick_spL (rev k)) eL (dce sH used_after) kL t m lL mcL (compile_post eH sH kH kL mcH mcL used_after postH).
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
        eapply H3 in H6.
        fwd.
        let Heq := fresh in
        pose proof H6p0 as Heq;
        eapply map.putmany_of_list_zip_sameLength, map.sameLength_putmany_of_list in Heq.
        fwd.
        eexists.
        split.
        * eapply H6.
        * intros. solve_compile_post.
          repeat listset_to_set. subset_union_solve.
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
        -- eapply agree_on_refl.
        -- intros. rewrite associate_one_left. rewrite H6. rewrite dfix_step.
           simpl. rewrite rev_app_distr. simpl. rewrite H0.
           rewrite <- app_assoc. reflexivity. 
      + intros.
        unfold compile_post in *.
        fwd. eapply H4 in H7p0. fwd.
        let Heq := fresh in
        pose proof H7p0p1 as Heq;
        eapply map.putmany_of_list_zip_sameLength,  map.sameLength_putmany_of_list in H7p0p1. fwd.
        exists retvs. eexists. repeat split.
        * erewrite agree_on_getmany.
          -- eapply H7p0p0.
          -- listset_to_set. agree_on_solve.
        * eapply H7p0p1.
        * solve_compile_post.
          -- agree_on_solve. repeat listset_to_set. subset_union_solve.
          -- simpl. rewrite H0. rewrite H7p5. reflexivity.
    - intros.
      eapply agree_on_find in H3; fwd.
      destr (existsb (eqb x) used_after); fwd.
      + eapply @exec.load.
        * rewrite <- H3p1. eassumption.
        * eauto.
        * solve_compile_post. simpl. rewrite E. reflexivity.
      + eapply @exec.skip.
        * solve_compile_post. simpl. rewrite E. reflexivity.
    - intros. repeat listset_to_set.
      eapply agree_on_union in H4; fwd.
      all: try solve [ eauto using String.eqb_spec ].
      eapply @exec.store.
      + erewrite <- H4p0; eauto.
        unfold elem_of; destr (a =? v)%string; eapply in_eq.
      + erewrite <- H4p0; eauto.
        unfold elem_of; destr (a =? v)%string; [ eapply in_eq | eapply in_cons, in_eq ].
      + eassumption.
      + solve_compile_post.
    - intros.
      eapply agree_on_find in H4; fwd.
      destr (existsb (eqb x) used_after); fwd.
      + eapply @exec.inlinetable; eauto.
        * rewrite <- H4p1. eassumption.
        * solve_compile_post. simpl. rewrite E. reflexivity.
      + eapply @exec.skip; eauto.
        solve_compile_post. simpl. rewrite E. reflexivity.
    - intros.
      repeat listset_to_set.
      eapply @exec.stackalloc.
      * eassumption.
      * intros. assert (H4' := H4 nil). rewrite dfix_step in H4'. simpl in H4'.
        rewrite app_nil_r in H4'. rewrite H4' in H2.
        eapply H2 with (used_after := used_after) (lL :=  (map.put lL x a)) in H5; subst a.
        2: eapply H6.
        -- eapply exec.weaken. 1: eapply H5. intros.
           unfold compile_post in H7. fwd. eexists. eexists.
           split; [eassumption|]. split; [eassumption|].
           solve_compile_post. simpl. rewrite H7p5. reflexivity.
        -- agree_on_solve.
        -- intros. rewrite associate_one_left. rewrite H4. rewrite dfix_step. simpl.
           rewrite rev_app_distr. simpl. repeat Tactics.destruct_one_match.
           repeat rewrite <- app_assoc. reflexivity.
    - intros. destr (existsb (eqb x) used_after).
      + eapply @exec.lit. solve_compile_post.
      + eapply @exec.skip. solve_compile_post.
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
          -- solve_compile_post. simpl. rewrite E.
             Tactics.destruct_one_match; reflexivity.
        * eapply @exec.skip. solve_compile_post. simpl. rewrite E.
          Tactics.destruct_one_match; reflexivity.
      + intros.
        eapply agree_on_find in H3; fwd.
        destr (existsb (eqb x) used_after).
        * eapply @exec.op.
          -- rewrite <- H3p1. eassumption.
          -- simpl. constructor.
          -- simpl in *. inversion H1. subst. solve_compile_post.
             simpl. rewrite E. Tactics.destruct_one_match; reflexivity.
        * eapply @exec.skip. solve_compile_post.
          simpl. rewrite E. Tactics.destruct_one_match; reflexivity.
    - intros.
      eapply agree_on_find in H2; fwd.
      repeat listset_to_set.
      destr (existsb (eqb x) used_after).
      { eapply @exec.set.
        - rewrite <- H2p1; eassumption.
        - solve_compile_post. }
      { eapply @exec.skip. solve_compile_post. }
    - intros.
      repeat listset_to_set.
      eapply agree_on_union in H2; fwd.
      eapply agree_on_union in H2p0; fwd.
      eapply @exec.if_true.
      + erewrite agree_on_eval_bcond; [ eassumption | ].
        pose agree_on_comm; eauto.
      + eapply @exec.weaken.
        -- eapply IHexec; eauto. intros. rewrite associate_one_left. rewrite H3.
           rewrite dfix_step. rewrite rev_app_distr. simpl.
           repeat Tactics.destruct_one_match. rewrite <- app_assoc. reflexivity.
        -- unfold compile_post. intros. fwd. solve_compile_post.
           simpl. rewrite H2p6. reflexivity.
    - intros.
      repeat listset_to_set.
      eapply agree_on_union in H2; fwd.
      eapply agree_on_union in H2p0; fwd.
      eapply @exec.if_false.
      + erewrite agree_on_eval_bcond; [ eassumption | ].
        pose agree_on_comm; eauto.
      + eapply @exec.weaken.
        -- eapply IHexec; eauto. intros. rewrite associate_one_left. rewrite H3.
           rewrite dfix_step. rewrite rev_app_distr. simpl.
           repeat rewrite <- app_assoc. repeat Tactics.destruct_one_match.
           reflexivity.
        -- unfold compile_post. intros. fwd. solve_compile_post.
           simpl. rewrite H2p6. reflexivity.
    - intros.
      cbn - [live].
      rename IHexec into IH1.
      rename H6 into IH12.
      rename H4 into IH2.
      cbn - [live] in IH12.
      eapply exec.loop_cps.
      eapply exec.weaken.
      { eapply IH1.
        - eapply agree_on_subset.
          + let Heq := fresh in
            specialize (live_while body1 cond body2 used_after) as Heq; cbn zeta in Heq.
            eapply H4.
          + eapply H7.
        - intros. rewrite H8. rewrite dfix_step. reflexivity. }
      intros. unfold compile_post in *. fwd.
      specialize H1 with (1 := H4p0). specialize H2 with (1 := H4p0).
      assert (H4: eval_bcond lH' cond = eval_bcond l' cond).
      { intros.
        unfold compile_post in *.
        fwd.
        apply agree_on_eval_bcond.
        repeat listset_to_set.
        apply agree_on_union in H4p1.
        fwd.
        eapply agree_on_subset; [ | eapply H4p1p1 ].
        subset_union_solve.
      }
      rewrite -> H4 in *.
      destruct (eval_bcond l' cond) as [b|] eqn:E; try congruence. exists b.
      split; [reflexivity|]. split.
      { intros. subst. solve_compile_post. rewrite <- app_assoc. simpl. rewrite H4p5.
        cbv [FixEq.Let_In_pf_nd]. rewrite List.skipn_app_r by reflexivity.
        simpl. rewrite <- app_assoc. reflexivity. }
      { intros. subst.
        eapply exec.weaken.
        { eapply IH2; eauto.
          - repeat listset_to_set.
            eapply agree_on_subset; [ | eapply H4p1 ].
            subset_union_solve.
          - intros. rewrite associate_one_left. rewrite app_assoc. rewrite H8.
            repeat (rewrite rev_app_distr || cbn [rev List.app] || rewrite <- app_assoc).
            rewrite dfix_step. cbn [stmt_leakage_body]. rewrite H4p5.
            cbv [FixEq.Let_In_pf_nd]. rewrite List.skipn_app_r by reflexivity.
            reflexivity.
        }
        cbv beta. intros. fwd.
        eapply exec.weaken.
        { eapply IH12; [eassumption|eassumption|].
          intros. rewrite associate_one_left. repeat rewrite app_assoc. rewrite H8.
          repeat (rewrite rev_app_distr || cbn [rev List.app] || rewrite <- app_assoc).
          f_equal. f_equal. rewrite dfix_step. cbn [stmt_leakage_body]. rewrite H4p5.
          cbv [FixEq.Let_In_pf_nd]. rewrite List.skipn_app_r by reflexivity.
          f_equal. f_equal. rewrite H6p5. rewrite List.skipn_app_r by reflexivity.
          reflexivity. }
        cbv beta. intros. fwd. solve_compile_post. cbn [stmt_leakage_body].
        repeat (rewrite rev_app_distr || cbn [rev List.app] || rewrite <- app_assoc).
        rewrite H4p5. f_equal. cbv [FixEq.Let_In_pf_nd].
        rewrite List.skipn_app_r by reflexivity. f_equal. rewrite H6p5.
        rewrite List.skipn_app_r by reflexivity. rewrite H6p9. reflexivity. }
    - intros.
      eapply @exec.seq.
      + eapply IHexec; [eassumption|].
        intros. rewrite H4. rewrite dfix_step. reflexivity.
      + unfold compile_post. intros. fwd.
        eapply @exec.weaken.
        * eapply H2; [eassumption|eassumption|].
          intros. rewrite app_assoc. rewrite H4.
          repeat rewrite rev_app_distr. rewrite dfix_step. simpl.
          rewrite H5p5. rewrite List.skipn_app_r by reflexivity.
          rewrite <- app_assoc. reflexivity.
        * unfold compile_post. intros. fwd. solve_compile_post.
          simpl. rewrite <- app_assoc. rewrite H5p5.
          rewrite List.skipn_app_r by reflexivity. rewrite H5p9.
          repeat rewrite <- app_assoc. reflexivity.
    - intros. eapply @exec.skip. solve_compile_post.
  Qed.
End WithArguments1.
