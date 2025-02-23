Require Import Coq.ZArith.ZArith.
Require Import coqutil.sanity coqutil.Macros.subst coqutil.Macros.unique coqutil.Byte.
Require Import coqutil.Datatypes.PrimitivePair coqutil.Datatypes.HList.
Require Import coqutil.Decidable.
Require Import coqutil.Tactics.fwd coqutil.Tactics.Tactics.
Require Import bedrock2.Syntax.
Require Import coqutil.Map.Interface coqutil.Map.Properties coqutil.Map.OfListWord.
Require Import coqutil.Word.Interface coqutil.Word.Bitwidth.
Require Import bedrock2.MetricLogging.
Require Import bedrock2.Memory bedrock2.ptsto_bytes bedrock2.Map.Separation.
Require Import bedrock2.Semantics bedrock2.MetricSemantics.
Require Import bedrock2.Map.DisjointUnion bedrock2.Map.split_alt.

Require Import Coq.Lists.List.

Section semantics.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word byte}.
  Context {locals: map.map String.string word}.
  Context {ext_spec: ExtSpec}.
  Context {mem_ok: map.ok mem} {word_ok: word.ok word}.

  Lemma frame_load: forall mSmall mBig mAdd a r (v: word),
      mmap.split mBig mSmall mAdd ->
      load a mSmall r = Some v ->
      load a mBig r = Some v.
  Proof.
    unfold load, load_Z. intros. fwd. eapply sep_of_load_bytes in E0.
    2: destruct a; simpl; destruct width_cases as [W | W]; rewrite W; cbv; discriminate.
    fwd. unfold sep in E0. fwd.
    eapply map.split_alt in E0p0.
    unfold mmap.split in *.
    rewrite E0p0 in H.
    rewrite mmap.du_assoc in H. unfold mmap.du in H at 1. fwd.
    erewrite load_bytes_of_sep. 1: reflexivity.
    unfold sep. do 2 eexists.
    rewrite map.split_alt.
    unfold mmap.split.
    ssplit. 2: eassumption. all: simpl; exact H.
  Qed.

  (* TODO share with FlatToRiscvCommon *)

  Lemma store_bytes_preserves_footprint: forall n a v (m m': mem),
      Memory.store_bytes n m a v = Some m' ->
      map.same_domain m m'.
  Proof using word_ok mem_ok.
    intros. unfold store_bytes, load_bytes, unchecked_store_bytes in *. fwd.
    eapply map.putmany_of_tuple_preserves_domain; eauto.
  Qed.

  Lemma disjoint_putmany_preserves_store_bytes: forall n a vs (m1 m1' mq: mem),
      store_bytes n m1 a vs = Some m1' ->
      map.disjoint m1 mq ->
      store_bytes n (map.putmany m1 mq) a vs = Some (map.putmany m1' mq).
  Proof using word_ok mem_ok.
    intros.
    unfold store_bytes, load_bytes, unchecked_store_bytes in *. fwd.
    erewrite map.getmany_of_tuple_in_disjoint_putmany by eassumption.
    f_equal.
    set (ks := (footprint a n)) in *.
    rename mq into m2.
    rewrite map.putmany_of_tuple_to_putmany.
    rewrite (map.putmany_of_tuple_to_putmany n m1 ks vs).
    apply map.disjoint_putmany_commutes.
    pose proof map.getmany_of_tuple_to_sub_domain _ _ _ _ E as P.
    apply map.sub_domain_value_indep with (vs2 := vs) in P.
    set (mp := (map.putmany_of_tuple ks vs map.empty)) in *.
    apply map.disjoint_comm.
    eapply map.sub_domain_disjoint; eassumption.
  Qed.

  Lemma store_bytes_frame: forall {n: nat} {m1 m1' m: mem} {a: word} {v: HList.tuple byte n} {F},
      Memory.store_bytes n m1 a v = Some m1' ->
      (eq m1 * F)%sep m ->
      exists m', (eq m1' * F)%sep m' /\ Memory.store_bytes n m a v = Some m'.
  Proof using word_ok mem_ok.
    intros.
    unfold sep in H0.
    destruct H0 as (mp & mq & A & B & C).
    subst mp.
    unfold map.split in A. destruct A as [A1 A2].
    eexists (map.putmany m1' mq).
    split.
    - unfold sep.
      exists m1', mq. repeat split; trivial.
      apply store_bytes_preserves_footprint in H.
      clear -H A2.
      unfold map.disjoint, map.same_domain, map.sub_domain in *. destruct H as [P Q].
      intros.
      edestruct Q; eauto.
    - subst m.
      eauto using disjoint_putmany_preserves_store_bytes.
  Qed.

  Lemma frame_store: forall sz (mSmall mSmall' mBig mAdd: mem) a v,
      mmap.split mBig mSmall mAdd ->
      store sz mSmall a v = Some mSmall' ->
      exists mBig', mmap.split mBig' mSmall' mAdd /\ store sz mBig a v = Some mBig'.
  Proof.
    intros. eapply (store_bytes_frame (F := eq mAdd)) in H0.
    2: {
      unfold sep. do 2 eexists. ssplit. 2,3: reflexivity. eapply map.split_alt; exact H.
    }
    fwd. unfold store, store_Z. rewrite H0p1. eexists. split. 2: reflexivity.
    unfold sep in H0p0. fwd. eapply map.split_alt. assumption.
  Qed.

  Lemma frame_eval_expr: forall l e mSmall mBig mAdd mc (v: word) mc',
      mmap.split mBig mSmall mAdd ->
      eval_expr mSmall l e mc = Some (v, mc') ->
      eval_expr mBig l e mc = Some (v, mc').
  Proof.
    induction e; cbn; intros; fwd; try reflexivity;
      erewrite ?IHe by eassumption;
      erewrite ?IHe1 by eassumption;
      try match goal with
        | |- context[word.eqb ?L ?R] => destr (word.eqb L R)
        end;
      erewrite ?IHe2 by eassumption;
      erewrite ?IHe3 by eassumption;
      erewrite ?frame_load by eassumption;
      rewrite_match;
      try reflexivity.
  Qed.

  Lemma frame_evaluate_call_args_log: forall l mSmall mBig mAdd arges
                                             mc (args: list word) mc',
      mmap.split mBig mSmall mAdd ->
      eval_call_args mSmall l arges mc = Some (args, mc') ->
      eval_call_args mBig   l arges mc = Some (args, mc').
  Proof.
    induction arges; cbn; intros.
    - assumption.
    - fwd. erewrite frame_eval_expr by eassumption. erewrite IHarges.
      1: reflexivity. all: assumption.
  Qed.

  Lemma frame_exec: forall e c t mSmall l mc P,
      exec e c t mSmall l mc P ->
      forall mBig mAdd,
        mmap.split mBig mSmall mAdd ->
        exec e c t mBig l mc (fun t' mBig' l' mc' =>
          exists mSmall', mmap.split mBig' mSmall' mAdd /\ P t' mSmall' l' mc').
  Proof.
    induction 1; intros;
      try match goal with
        | H: store _ _ _ _ = _ |- _ => eapply frame_store in H; [ | eassumption]
        end;
      fwd;
      try solve [econstructor; eauto using frame_eval_expr].
    { eapply exec.stackalloc. 1: eassumption.
      intros.
      rename mCombined into mCombinedBig.
      specialize H1 with (1 := H3).
      specialize (H1 (mmap.force (mmap.du (mmap.Def mSmall) (mmap.Def mStack)))).
      eapply map.split_alt in H4. pose proof H4 as D0. unfold mmap.split in D0.
      rewrite H2 in D0.
      rewrite (mmap.du_comm (mmap.Def mSmall) (mmap.Def mAdd)) in D0.
      rewrite mmap.du_assoc in D0. unfold mmap.du at 1 in D0.
      unfold mmap.of_option in D0. fwd. rename r into mCombinedBig.
      symmetry in E0. rename E0 into D0.
      eapply exec.weaken. 1: eapply H1.
      { simpl. eapply map.split_alt. unfold mmap.split. symmetry. assumption. }
      { unfold mmap.split. simpl. rewrite map.du_comm. unfold mmap.of_option.
        rewrite <- D0. reflexivity. }
      cbv beta. intros. fwd.
      move D0 at bottom.
      repeat match reverse goal with
             | H: map.split _ _ _ |- _ => eapply map.split_alt in H
             | H: mmap.split _ _ _ |- _ =>
                 unfold mmap.split in H;
                 let F := fresh "D0" in
                 rename H into F;
                 move F at bottom
             end.
      rewrite D1 in D2. clear D1 mBig. rewrite D4 in D3. clear D4 mSmall'.
      rewrite mmap.du_assoc in D3. rewrite (mmap.du_comm mStack') in D3.
      rewrite <- mmap.du_assoc in D3.
      eexists (mmap.force (mmap.du mSmall'0 mAdd)). exists mStack'. ssplit.
      1: eassumption.
      { simpl. eapply map.split_alt. unfold mmap.split.
        rewrite D3. f_equal. unfold mmap.du at 1 in D3. fwd. simpl in E0. rewrite E0.
        reflexivity. }
      eexists; split. 2: eassumption.
      unfold mmap.split. simpl.
      unfold mmap.du at 1 in D3. fwd. simpl in E0. rewrite E0. reflexivity. }
    { eapply exec.seq. 1: eapply IHexec; eassumption.
      cbv beta. intros. fwd. eapply H1. 1: eassumption. assumption. }
    { eapply exec.while_true.
      1: eauto using frame_eval_expr.
      1: eassumption.
      { eapply IHexec. 1: eassumption. }
      cbv beta. intros. fwd. eauto. }
    { (* call *)
      econstructor. 1: eassumption.
      { eauto using frame_evaluate_call_args_log. }
      1: eassumption.
      1: eapply IHexec. 1: eassumption.
      cbv beta. intros. fwd.
      specialize H3 with (1 := H5p1). fwd. eauto 10. }
    { (* interact *)
      eapply map.split_alt in H. pose proof H3 as A.
      unfold mmap.split in H3, H. rewrite H in H3.
      rewrite mmap.du_assoc in H3. rewrite (mmap.du_comm mGive) in H3.
      rewrite <- mmap.du_assoc in H3.
      assert (exists mKeepBig, mmap.Def mKeepBig = mmap.du mKeep mAdd) as Sp0. {
        exists (mmap.force (mmap.du mKeep mAdd)).
        unfold mmap.du in H3 at 1. unfold mmap.of_option in *.
        fwd. simpl in E. unfold mmap.of_option in E. fwd. reflexivity.
      }
      destruct Sp0 as (mKeepBig & Sp0).
      assert (mmap.split mBig mKeepBig mGive) as Sp.
      { unfold mmap.split. rewrite Sp0. assumption. }
      econstructor. 1: eapply map.split_alt; exact Sp.
      { eauto using frame_evaluate_call_args_log. }
      1: eassumption.
      intros.
      specialize H2 with (1 := H4). fwd.
      eexists. split. 1: eassumption.
      intros.
      eapply map.split_alt in H2. unfold mmap.split in *.
      assert (exists mSmall', mmap.split mSmall' mKeep mReceive) as Sp1. {
        exists (mmap.force (mmap.du mKeep mReceive)).
        eapply map.split_alt. rewrite Sp0 in H2.
        rewrite mmap.du_assoc in H2. rewrite (mmap.du_comm mAdd) in H2.
        rewrite <- mmap.du_assoc in H2.
        unfold mmap.du at 1 in H2. fwd.
        eapply map.split_alt. unfold mmap.split. simpl in E. simpl. rewrite E. reflexivity.
      }
      destruct Sp1 as (mSmall' & Sp1).
      exists mSmall'. split. 2: eapply H2p1.
      2: { eapply map.split_alt. exact Sp1. }
      rewrite Sp0 in H2.
      unfold mmap.split in Sp1. rewrite Sp1. rewrite mmap.du_assoc in H2.
      rewrite (mmap.du_comm mAdd) in H2. rewrite <- mmap.du_assoc in H2.
      exact H2.
    }
  Qed.

End semantics.

Require Import bedrock2.Semantics.

Section semantics.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word byte}.
  Context {locals: map.map String.string word}.
  Context {ext_spec: ExtSpec}.
  Context {mem_ok: map.ok mem} {word_ok: word.ok word}.
  Print mmap.

  Lemma sub_domain_disj {k v} {map : map.map k v} (m mSmall mAdd1 mAdd2 : map) :
    map.disjoint mAdd1 mAdd2 ->
    map.sub_domain m (map.putmany mSmall mAdd1) ->
    map.sub_domain m (map.putmany mSmall mAdd2) ->
    map.sub_domain m mSmall.
  Proof. Admitted.

  Lemma sub_split {k v} {map : map.map k v} (mBig mSmall mAdd m garbage : map) :
    map.split mBig mSmall mAdd ->
    map.sub_domain m mSmall ->
    map.split mBig m garbage ->
    exists garbage',
      map.split mSmall m garbage'.
  Proof. Admitted.

  Lemma intersect_load_bytes: forall mSmall (mBig1 mBig2 mAdd1 mAdd2 : mem) sz a v v0,
      map.split mBig1 mSmall mAdd1 ->
      map.split mBig2 mSmall mAdd2 ->
      map.disjoint mAdd1 mAdd2 ->
      load_bytes (bytes_per (width := width) sz) mBig1 a = Some v0 ->
      load_bytes (bytes_per (width := width) sz) mBig2 a = Some v ->
      load_bytes (bytes_per (width := width) sz) mSmall a = Some v.
  Proof.
    intros *. intros  ? ? ? E0 E1. eapply sep_of_load_bytes in E0, E1.
    2,3: destruct sz; simpl; destruct width_cases as [W | W]; rewrite W; cbv; discriminate.
    fwd. unfold sep in E0, E1. fwd.
    Search ptsto_bytes.
    assert (H2: map.sub_domain mp mp0).
    { clear -mem_ok word_ok BW E0p1 E1p1.
      apply ptsto_bytes_iff_eq_of_list_word_at in E0p1, E1p1.
      2,3: destruct sz; simpl; destruct width_cases as [W | W]; rewrite W; cbv; discriminate.
      repeat intro. assert (H': map.get mp k <> None) by congruence.
      enough (map.get mp0 k <> None).
      { destruct (map.get mp0 k); eauto || congruence. }
      subst. Search map.of_list_word_at. apply map.get_of_list_word_at_domain in H'.
      apply map.get_of_list_word_at_domain. Search (length (tuple.to_list _)).
      rewrite tuple.length_to_list in *. assumption. }
    (*clear H3.*) clear E0p2 E1p2 R.
    assert (H3: map.sub_domain mp mBig1 /\ map.sub_domain mp mBig2).
    { split.
      - destruct E0p0 as [? _]; subst. apply map.sub_domain_putmany_r. assumption.
      - destruct E1p0 as [? _]; subst. apply map.sub_domain_putmany_r. apply map.sub_domain_refl. }
    clear H2.
    assert (H4: map.sub_domain mp mSmall).
    { fwd. destruct H, H0; subst. eapply sub_domain_disj; eauto. }

    erewrite load_bytes_of_sep; [reflexivity|].
    pose proof (@sub_split _ _ mem) as H'.
    specialize H' with (1 := H0) (2 := H4) (3 := E1p0). destruct H' as [garbage' H'].
    exists mp, garbage'. split; [assumption|]. split; [assumption|].
    instantiate (1 := fun _ => True). exact I.
  Qed.
  
  Lemma intersect_load: forall mSmall mBig1 mBig2 mAdd1 mAdd2 a r (v v0: word),
      map.split mBig1 mSmall mAdd1 ->
      map.split mBig2 mSmall mAdd2 ->
      map.disjoint mAdd1 mAdd2 ->
      load a mBig1 r = Some v ->
      load a mBig2 r = Some v0 ->
      load a mSmall r = Some v0.
  Proof.
    unfold load, load_Z. intros. fwd. pose proof intersect_load_bytes as H'.
    specialize H' with (1 := H) (2 := H0) (3 := H1) (4 := E1) (5 := E0).
    rewrite H'. reflexivity.
  Qed.

  Lemma intersect_store_bytes sz (mBig1 mBig2 mBig1' mBig2' mSmall mAdd1 mAdd2 : mem) a v :
      map.split mBig1 mSmall mAdd1 ->
      map.split mBig2 mSmall mAdd2 ->
      map.disjoint mAdd1 mAdd2 ->
      Memory.store_bytes (bytes_per (width := width) sz) mBig1 a v = Some mBig1' ->
      Memory.store_bytes (bytes_per (width := width) sz) mBig2 a v = Some mBig2' ->
      exists mSmall',
        Memory.store_bytes (bytes_per (width := width) sz) mSmall a v = Some mSmall' /\
          map.split mBig1' mSmall' mAdd1.
    Proof.
      intros. Check disjoint_putmany_preserves_store_bytes.
      enough (exists mSmall', store_bytes _ mSmall a v = Some mSmall') as [mSmall' H'].
      { exists mSmall'. split; [assumption|].
        destruct H as [? Hdisj]; subst.
        pose proof disjoint_putmany_preserves_store_bytes as H''.
        specialize H'' with (1 := H') (2 := Hdisj).
        rewrite H2 in H''. inversion H''. subst. clear H''. split; [reflexivity|].
        Search map.sub_domain. eapply map.sub_domain_disjoint; [eassumption|].
        Search store_bytes. apply store_bytes_preserves_footprint in H'.
        apply H'. }
      unfold store_bytes in H2,H3. destruct_one_match_hyp; [|congruence].
      destruct_one_match_hyp; [|congruence]. Search (load_bytes).
      pose proof intersect_load_bytes as H'.
      specialize H' with (1 := H) (2 := H0) (3 := H1) (4 := E0) (5 := E).
      unfold store_bytes. rewrite H'. eexists. reflexivity.
    Qed.

    Lemma intersect_store: forall sz (mSmall mBig1 mBig2 mBig1' mBig2' mAdd1 mAdd2: mem) a v,
        map.disjoint mAdd1 mAdd2 ->
        map.split mBig1 mSmall mAdd1 ->
        map.split mBig2 mSmall mAdd2 ->
        store sz mBig1 a v = Some mBig1' ->
        store sz mBig2 a v = Some mBig2' ->
        exists mSmall',
          store sz mSmall a v = Some mSmall' /\
            map.split mBig1' mSmall' mAdd1.
  Proof.
    intros. unfold store, store_Z in H2, H3.
    remember (LittleEndianList.le_split _ _) as x.
    pose proof intersect_store_bytes as H'.
    specialize H' with (1 := H0) (2 := H1) (3 := H). remember (tuple.of_list x) as y.
    set (z := length x). specialize (H' sz).
    replace (bytes_per sz) with (length x) in H'.
    2: { subst. Search (length (LittleEndianList.le_split _ _)). apply LittleEndianList.length_le_split. }
    specialize H' with (1 := H2) (2 := H3).
    destruct H' as (mSmall'&H1'&H2').
    exists mSmall'. split; [|assumption]. unfold store, store_Z. subst. assumption.
  Qed.
  
  Lemma intersect_eval_expr: forall l e mSmall mBig1 mBig2 mAdd1 mAdd2 (v v0: word),
      map.disjoint mAdd1 mAdd2 ->
      map.split mBig1 mSmall mAdd1 ->
      map.split mBig2 mSmall mAdd2 ->
      eval_expr mBig1 l e = Some v ->
      eval_expr mBig2 l e = Some v0 ->
      (v = v0 /\ eval_expr mSmall l e = Some v).
  Proof.
    intros * H1 H2 H3. revert v v0.
    induction e; cbn; intros; fwd; auto;
      repeat match goal with
      | IHe: forall _ _, _ = _ -> _ = _ -> _ |- _ =>
          specialize (IHe _ _ eq_refl eq_refl); destruct IHe as [?IHe1 ?IHe2];
          subst; repeat rewrite ?IHe2
        end.
    - rewrite H in H0. inversion H0. subst. auto.
    - pose proof intersect_load as H'.
      specialize H' with (1 := H2) (2 := H3) (3 := H1) (4 := H) (5 := H0).
      pose proof intersect_load as H''.
      Search map.disjoint. apply map.disjoint_comm in H1.
      specialize H'' with (1 := H3) (2 := H2) (3 := H1) (4 := H0) (5 := H).
      rewrite H' in H''. inversion H''. subst. auto.
    - rewrite H in H0. inversion H0. subst. auto.
    - rewrite IHe0. auto.
    - rewrite IHe0. match goal with
      | |- context[word.eqb ?L ?R] => destr (word.eqb L R)
      end; eauto.
  Qed.

  Lemma intersect_eval_expr': forall l e mSmall mBig1 mBig2 mAdd1 mAdd2 (v v0: word),
      map.disjoint mAdd1 mAdd2 ->
      map.split mBig1 mSmall mAdd1 ->
      map.split mBig2 mSmall mAdd2 ->
      eval_expr mBig1 l e = Some v ->
      eval_expr mBig2 l e = Some v0 ->
      eval_expr mSmall l e = Some v.
  Proof. apply intersect_eval_expr. Qed.

  Lemma intersect_evaluate_call_args_log: forall  arges
                                             (args args0: list word),
      forall l mSmall mBig1 mBig2 mAdd1 mAdd2,
      map.split mBig1 mSmall mAdd1 ->
      map.split mBig2 mSmall mAdd2 ->
      map.disjoint mAdd1 mAdd2 ->
      eval_call_args mBig1 l arges = Some args ->
      eval_call_args mBig2 l arges = Some args0 ->
      eval_call_args mSmall l arges = Some args.
  Proof.
    induction arges; cbn; intros.
    - assumption.
    - fwd.
      specialize intersect_eval_expr with (1 := H1) (2 := H) (3 := H0) (4 := E1) (5 := E).
      intros [H1' H2']. rewrite H2'. subst. erewrite IHarges.
      1: reflexivity. 3: eassumption. all: eassumption.
  Qed.

  Ltac speck H0 :=
    repeat match goal with | H: _ |- _ => specialize H0 with (1 := H) end.

  Lemma split_sub_domain (m m1 m2 m' m1' m2' : mem) :
    map.split m m1 m2 ->
    map.split m' m1' m2' ->
    map.sub_domain m m' ->
    map.sub_domain m1' m1 ->
    map.sub_domain m2 m2'.
  Proof.
    intros H1 H2 H3 H4. repeat intro. Search map.split.
    pose proof map.get_split_grow_l as Hm. specialize Hm with (1 := H1) (2 := H).
    pose proof map.get_split as Hm'. specialize Hm' with (1 := H1). specialize (Hm' k).
    destruct Hm' as [Hm'|Hm']; [fwd; congruence|]. destruct Hm' as [_ Hm'].
    apply H3 in Hm. fwd. pose proof map.get_split as Hm'0. specialize (Hm'0 k).
    specialize Hm'0 with (1 := H2). destruct Hm'0 as [Hm'0 | Hm'0].
    - fwd. exfalso. rewrite Hm'0p0 in Hm. apply H4 in Hm. fwd. congruence.
    - fwd. rewrite Hm'0p0 in Hm. eexists. eapply Hm.
  Qed.

  Lemma split_same_domain (m m1 m2 m' m1' m2' : mem) :
    map.split m m1 m2 ->
    map.split m' m1' m2' ->
    map.same_domain m m' ->
    map.same_domain m1' m1 ->
    map.same_domain m2 m2'.
  Proof. intros. destruct H1, H2. split; eauto using split_sub_domain. Qed.
                          
  Lemma intersect_same_domain e c t m l post :
    exec e c t m l post ->
    exec e c t m l (fun t' m' l' => post t' m' l' /\ map.same_domain m m').
  Proof.
    intros H. induction H; try solve [econstructor; eauto using map.same_domain_refl].
    - econstructor; eauto. split; [assumption|]. eapply store_preserves_domain.
      eassumption.
    - econstructor; eauto. intros. eapply exec.weaken. 1: eapply H1; eauto.
      simpl. intros. fwd. do 2 eexists. intuition eauto.
      eapply (split_same_domain mCombined _ _ m' _ _).
      { eapply map.split_comm. eassumption. }
      { eapply map.split_comm. eassumption. }
      { assumption. }
      { eapply anybytes_unique_domain; eassumption. }
    - econstructor; eauto. simpl. intros. fwd. eapply exec.weaken.
      1: eapply H1; assumption.
      simpl. intros. fwd. split; auto. eapply map.same_domain_trans; eauto.
    - eapply exec.while_true; eauto. simpl. intros. fwd. eapply exec.weaken.
      1: eapply H3; assumption.
      simpl. intros. fwd. split; auto. eapply map.same_domain_trans; eauto.
    - econstructor; eauto. simpl. intros. fwd. apply H3 in H4p0. fwd. eauto 10.
    - econstructor; eauto. intros. apply H2 in H3. fwd. eexists. intuition eauto.
      Abort.

  (*this is not true---we need an enough-stack-space hypothesis for execution number 2.
    after all, exec e c t mBig2 l P2 says nothing useful if mBig2 is the whole address
    space and c is a stackalloc.*)
  Lemma intersect_exec: forall e c t mBig1 mBig2 mAdd1 mAdd2 mSmall l P1 P2,
      map.split mBig1 mSmall mAdd1 ->
      map.split mBig2 mSmall mAdd2 ->
      map.disjoint mAdd1 mAdd2 ->
      exec e c t mBig1 l P1 ->
      exec e c t mBig2 l P2 ->
      exec e c t mBig1 l (fun t' mBig1' l' =>
                            P1 t' mBig1' l' /\
                              exists mSmall', map.split mBig1' mSmall' mAdd1).
  Proof.
    intros. revert H.
    pose proof intersect_eval_expr as Hint. specialize Hint with (1 := H1) (3 := H0).
    induction H2; inversion H3; subst; intros H''; specialize Hint with (1 := H'');
      pose proof Hint as Hint';
      repeat match goal with
        | H: eval_expr _ _ _ = _ |- _ => specialize Hint' with (1 := H)
        end;
      fwd;
      try solve [econstructor; eauto].
    - specialize Hint with (1 := H). speck Hint. fwd. pose proof intersect_store as store.
      speck store. fwd. econstructor; eauto.
    - econstructor; eauto. intros. eapply exec.weaken.
      Search exec.
      1: eapply H4; eauto.
      { Check H3. inversion H3. subst. assumption. simpl. intros. fwd. eexists. eexists. intuition eauto.
      eexists. eauto.
      + intersect_store; e.auto.
    induction 4; intros; fwd;
      pose proof intersect_eval_expr as H';
      speck H'; try solve [econstructor; eauto].
    - econstructor; eauto. inversion H4. subst. eapply intersect_eval_expr; eauto.
    - inversion H6. subst. pose proof intersect_eval_expr as H'. speck H'. fwd.
      clear H2 H10. pose proof intersect_eval_expr as H'. speck H'. fwd.
      
      econstructor; eauto using intersect_eval_expr'.
      + edestruct intersect_store; eauto. 3: eauto.
      1: eapply intersect_eval_expr; eauto.
    try solve [econstructor; eauto using 
      try match goal with
        | H: store _ _ _ _ = _ |- _ => eapply frame_store in H; [ | eassumption]
        end;
      fwd;
      try solve [econstructor; eauto using frame_eval_expr].
    { eapply exec.stackalloc. 1: eassumption.
      intros.
      rename mCombined into mCombinedBig.
      specialize H1 with (1 := H3).
      specialize (H1 (mmap.force (mmap.du (mmap.Def mSmall) (mmap.Def mStack)))).
      eapply map.split_alt in H4. pose proof H4 as D0. unfold mmap.split in D0.
      rewrite H2 in D0.
      rewrite (mmap.du_comm (mmap.Def mSmall) (mmap.Def mAdd)) in D0.
      rewrite mmap.du_assoc in D0. unfold mmap.du at 1 in D0.
      unfold mmap.of_option in D0. fwd. rename r into mCombinedBig.
      symmetry in E0. rename E0 into D0.
      eapply exec.weaken. 1: eapply H1.
      { simpl. eapply map.split_alt. unfold mmap.split. symmetry. assumption. }
      { unfold mmap.split. simpl. rewrite map.du_comm. unfold mmap.of_option.
        rewrite <- D0. reflexivity. }
      cbv beta. intros. fwd.
      move D0 at bottom.
      repeat match reverse goal with
             | H: map.split _ _ _ |- _ => eapply map.split_alt in H
             | H: mmap.split _ _ _ |- _ =>
                 unfold mmap.split in H;
                 let F := fresh "D0" in
                 rename H into F;
                 move F at bottom
             end.
      rewrite D1 in D2. clear D1 mBig. rewrite D4 in D3. clear D4 mSmall'.
      rewrite mmap.du_assoc in D3. rewrite (mmap.du_comm mStack') in D3.
      rewrite <- mmap.du_assoc in D3.
      eexists (mmap.force (mmap.du mSmall'0 mAdd)). exists mStack'. ssplit.
      1: eassumption.
      { simpl. eapply map.split_alt. unfold mmap.split.
        rewrite D3. f_equal. unfold mmap.du at 1 in D3. fwd. simpl in E0. rewrite E0.
        reflexivity. }
      eexists; split. 2: eassumption.
      unfold mmap.split. simpl.
      unfold mmap.du at 1 in D3. fwd. simpl in E0. rewrite E0. reflexivity. }
    { eapply exec.seq. 1: eapply IHexec; eassumption.
      cbv beta. intros. fwd. eapply H1. 1: eassumption. assumption. }
    { eapply exec.while_true.
      1: eauto using frame_eval_expr.
      1: eassumption.
      { eapply IHexec. 1: eassumption. }
      cbv beta. intros. fwd. eauto. }
    { (* call *)
      econstructor. 1: eassumption.
      { eauto using frame_evaluate_call_args_log. }
      1: eassumption.
      1: eapply IHexec. 1: eassumption.
      cbv beta. intros. fwd.
      specialize H3 with (1 := H5p1). fwd. eauto 10. }
    { (* interact *)
      eapply map.split_alt in H. pose proof H3 as A.
      unfold mmap.split in H3, H. rewrite H in H3.
      rewrite mmap.du_assoc in H3. rewrite (mmap.du_comm mGive) in H3.
      rewrite <- mmap.du_assoc in H3.
      assert (exists mKeepBig, mmap.Def mKeepBig = mmap.du mKeep mAdd) as Sp0. {
        exists (mmap.force (mmap.du mKeep mAdd)).
        unfold mmap.du in H3 at 1. unfold mmap.of_option in *.
        fwd. simpl in E. unfold mmap.of_option in E. fwd. reflexivity.
      }
      destruct Sp0 as (mKeepBig & Sp0).
      assert (mmap.split mBig mKeepBig mGive) as Sp.
      { unfold mmap.split. rewrite Sp0. assumption. }
      econstructor. 1: eapply map.split_alt; exact Sp.
      { eauto using frame_evaluate_call_args_log. }
      1: eassumption.
      intros.
      specialize H2 with (1 := H4). fwd.
      eexists. split. 1: eassumption.
      intros.
      eapply map.split_alt in H2. unfold mmap.split in *.
      assert (exists mSmall', mmap.split mSmall' mKeep mReceive) as Sp1. {
        exists (mmap.force (mmap.du mKeep mReceive)).
        eapply map.split_alt. rewrite Sp0 in H2.
        rewrite mmap.du_assoc in H2. rewrite (mmap.du_comm mAdd) in H2.
        rewrite <- mmap.du_assoc in H2.
        unfold mmap.du at 1 in H2. fwd.
        eapply map.split_alt. unfold mmap.split. simpl in E. simpl. rewrite E. reflexivity.
      }
      destruct Sp1 as (mSmall' & Sp1).
      exists mSmall'. split. 2: eapply H2p1.
      2: { eapply map.split_alt. exact Sp1. }
      rewrite Sp0 in H2.
      unfold mmap.split in Sp1. rewrite Sp1. rewrite mmap.du_assoc in H2.
      rewrite (mmap.du_comm mAdd) in H2. rewrite <- mmap.du_assoc in H2.
      exact H2.
    }
  Qed.

End semantics.
