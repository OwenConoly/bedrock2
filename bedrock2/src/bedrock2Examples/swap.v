Require Import bedrock2.NotationsCustomEntry coqutil.Macros.WithBaseName.
Require Import coqutil.Tactics.fwd.
Require Import Lia.
Import Syntax BinInt String List.ListNotations.
Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.

Definition swap := func! (a, b) {
  load1(t, b);
  load1(x0, a);
  store1(b, x0);
  store1(a, t)
}.

Definition bad_swap := func! (a, b) {
  load1(x0, a);
  store1(b, x0);
  load1(x1, b);
  store1(a, x1)
}.

Definition swap_swap := func! (a, b) {
  swap(a, b);
  swap(a, b)
}.

Require Import bedrock2.WeakestPrecondition.
Require Import bedrock2.Semantics.
Require Import coqutil.Map.Interface bedrock2.Map.Separation bedrock2.Map.SeparationLogic.

Require bedrock2.WeakestPreconditionProperties.
From coqutil.Tactics Require Import Tactics letexists eabstract.
Require Import bedrock2.ProgramLogic bedrock2.Scalars.
Require Import coqutil.Word.Interface.
Require Import coqutil.Tactics.rdelta.
Require Import bedrock2.MemList.
Check Scalars.load_one_of_sep.
Require Import coqutil.Map.Properties.
Require Import coqutil.Word.Bitwidth.

Section WithParameters.
  Context {BW: Bitwidth 32} {word: word.word 32} {mem: map.map word Byte.byte} {listmem: map.map (word * nat) Byte.byte} {locals: map.map String.string word}.
  Context {word_ok: word.ok word} {locals_ok: map.ok locals} {mem_ok: map.ok mem} {listmem_ok: map.ok listmem}.
  Context {ext_spec: ExtSpec} {ext_spec_ok: ext_spec.ok ext_spec}.
  Locate "=*".
  Instance spec_of_swap : spec_of "swap" :=
    fnspec! "swap" a_addr b_addr / a b R,
    { requires t m := m =* ptsto a_addr a * ptsto b_addr b * R;
      ensures T M :=  M =* ptsto a_addr b * ptsto b_addr a * R /\ T = t }.

  Check cmd. Print cmd.load.
  Check load_one_of_sep. Check dexpr.
  Lemma load_one_of_sep_memlist t m l addr value R x ea e  :
    m =* ptsto addr value * R ->
    dexpr l ea addr ->
    cmd e (cmd.load x access_size.one ea) t m l
      (fun t' m' l' => t' = t /\ m' = m /\ l' = map.put l x (of_bytes [value])).
  Proof.
    intros Hm Ha. cbn [cmd cmd_body]. exists addr. split; [assumption|].
    exists [value]. destruct Hm as (mLoad&mSmall&Hsplit&Hload&Hsmall).
    exists mLoad, mSmall. split; [reflexivity|]. split.
    { simpl. exists mLoad, map.empty. ssplit.
      - apply map.split_empty_r. reflexivity.
      - assumption.
      - cbv [emp]. auto. }
    auto.
  Qed. Check cmd.store.

  Lemma store_one_of_sep_memlist t m l addr val0 val R ea ev e :
    m =* ptsto addr val0 * R ->
    dexpr l ea addr ->
    dexpr l ev val ->
    cmd e (cmd.store access_size.one ea ev) t m l
      (fun t' m' l' =>
         t' = t /\ m' =* ptsto addr (Byte.byte.of_Z (word.unsigned val)) * R /\ l' = l).
  Proof.
    intros Hm Ha Hv. cbn [cmd cmd_body]. exists addr. split; [assumption|].
    exists val. split; [assumption|]. destruct Hm as (mStore&mSmall&Hsplit&Hstore&Hsmall).
    exists mStore. assert (Hstore' := Hstore). destruct Hstore as [n Hstore].
    exists (map.put map.empty (addr, n) (Byte.byte.of_Z (word.unsigned val))).
    exists mSmall. eexists. ssplit.
    - cbv [anybytes']. exists [val0]. split; [reflexivity|]. exists mStore, map.empty. ssplit.
      + apply map.split_empty_r. reflexivity.
      + assumption.
      + simpl. cbv [emp]. auto.
    - simpl. eexists. exists map.empty. ssplit.
      + apply map.split_empty_r. reflexivity.
      + exists n. reflexivity.
      + cbv [emp]. auto.
    - assumption.
    - cbv [map.split]. split; [reflexivity|]. destruct Hsplit as [_ Hdisj].
      eapply map.sub_domain_disjoint. 1: eassumption. subst. repeat intro.
      rewrite map.get_put_dec in H. destruct_one_match_hyp.
      + eexists. rewrite map.get_put_same. reflexivity.
      + Search map.get map.empty. rewrite map.get_empty in H. congruence.
    - reflexivity.
    - eexists. eexists. ssplit.
      + split. 1: reflexivity. destruct Hsplit as [_ Hdisj].
      eapply map.sub_domain_disjoint. 1: eassumption. subst. repeat intro.
      rewrite map.get_put_dec in H. destruct_one_match_hyp.
      -- eexists. rewrite map.get_put_same. reflexivity.
      -- Search map.get map.empty. rewrite map.get_empty in H. congruence.
      + exists n. reflexivity.
      + assumption.
    - reflexivity.
  Qed.
  
  Lemma cmd_seq e s1 s2 t m l post :
    cmd e (cmd.seq s1 s2) t m l post =
      cmd e s1 t m l
        (fun (t0 : trace) (m0 : listmem) (l0 : locals) => cmd e s2 t0 m0 l0 post).
  Proof. reflexivity. Qed.

  Lemma sep_assoc (m : listmem) R1 R2 R3 :
    m =* R1 * R2 * R3 <-> m =* R1 * (R2 * R3).
  Proof.
    split; intros H.
    - cbv [sep map.split] in *. fwd. exists mp0, (map.putmany mq0 mq).
      apply map.disjoint_putmany_l in Hp0p1. fwd. ssplit; eauto.
      + symmetry. apply map.putmany_assoc.
      + Search (map.disjoint _ (map.putmany _ _)). 
        apply map.disjoint_putmany_r. eauto.
      + eauto 10.
    - cbv [sep map.split] in *. fwd. exists (map.putmany mp mp0), mq0.
      apply map.disjoint_putmany_r in Hp0p1. fwd. ssplit; eauto.
      + apply map.putmany_assoc.
      + Search (map.disjoint _ (map.putmany _ _)). 
        apply map.disjoint_putmany_l. eauto.
      + eauto 10.
  Qed.

  Lemma sep_comm (m : listmem) R1 R2 :
    m =* R1 * R2 <-> m =* R2 * R1.
  Proof.
    split; intros H; cbv [sep map.split] in *; fwd.
    - exists mq, mp. intuition auto.  2: apply map.disjoint_comm; assumption.
      Search map.putmany. apply map.putmany_comm. assumption.
    - exists mq, mp. intuition auto. 2: apply map.disjoint_comm; assumption.
      apply map.putmany_comm. assumption.
  Qed.

  Lemma idk (m : listmem) R1 R1' R2 :
    (forall m, m =* R1 <-> m =* R1') ->
    m =* R1 * R2 <-> m =* R1' * R2.
  Proof.
    intros H. split; intros H'; cbv [sep] in *; fwd.
    - exists mp, mq. ssplit; try assumption. apply H. assumption.
    - exists mp, mq. ssplit; try assumption. apply H. assumption.
  Qed.

  Lemma byte_to_word_to_byte b :
    Byte.byte.of_Z (word.unsigned (word := word) (of_bytes [b])) = b.
  Proof.
    cbv [of_bytes]. cbv [LittleEndianList.le_combine].
    rewrite word.unsigned_of_Z. simpl. Search (Z.lor _ 0). rewrite Z.lor_0_r.
    Search Byte.byte.unsigned. rewrite wrap_byte_unsigned. Search Byte.byte.unsigned.
    rewrite Byte.byte.of_Z_unsigned. reflexivity.
  Qed.
    
  Lemma swap_ok : program_logic_goal_for_function! swap.
  Proof.
    (*first load*)
    repeat straightline. subst c1. rewrite cmd_seq.
    Print seprewrite_in. Print seprewrite0_in.
    erewrite idk in H.
    2: { intros. instantiate (1 := (ptsto b_addr b * ptsto a_addr a)%sep). apply sep_comm. }
    rewrite sep_assoc in H.
    eapply WeakestPreconditionProperties.Proper_cmd.
    2: { eapply load_one_of_sep_memlist. 1: eassumption.
         cbv [dexpr expr expr_body get]. eexists. subst l.
         rewrite map.get_put_same. auto. }
    (*second load*)
    cbv [Morphisms.pointwise_relation Basics.impl]. intros. fwd. subst c0.
    rewrite cmd_seq.
    rewrite <- sep_assoc in H. erewrite idk in H.
    2: { intros. instantiate (1 := (ptsto a_addr a * ptsto b_addr b)%sep).
         apply sep_comm. }
    rewrite sep_assoc in H.
    eapply WeakestPreconditionProperties.Proper_cmd.
    2: { eapply load_one_of_sep_memlist. 1: eassumption.
         cbv [dexpr expr expr_body get]. eexists. subst l.
         rewrite map.get_put_diff; [|congruence].
         rewrite map.get_put_diff; [|congruence].
         rewrite map.get_put_same. auto. }
    (*first store*)
    cbv [Morphisms.pointwise_relation Basics.impl]. intros. fwd. subst c.
    rewrite cmd_seq.
    rewrite <- sep_assoc in H. erewrite idk in H.
    2: { intros. instantiate (1 := (ptsto b_addr b * ptsto a_addr a)%sep).
         apply sep_comm. }
    rewrite sep_assoc in H.
    eapply WeakestPreconditionProperties.Proper_cmd.
    2: { eapply store_one_of_sep_memlist. 1: eassumption.
         - cbv [dexpr expr expr_body get]. eexists. subst l.
           rewrite map.get_put_diff by congruence.
           rewrite map.get_put_diff by congruence.
           rewrite map.get_put_same. auto.
         - cbv [dexpr expr expr_body get]. eexists. subst l.
           rewrite map.get_put_same. auto. }
    (*second store*)
    cbv [Morphisms.pointwise_relation Basics.impl].
    intros. fwd.
    rewrite <- sep_assoc in H0p1.
    erewrite idk in H0p1.
    2: { intros. instantiate (1 := (ptsto _ _ * ptsto _ _)%sep). apply sep_comm. }
    rewrite sep_assoc in H0p1.
    eapply WeakestPreconditionProperties.Proper_cmd.
    2: { eapply store_one_of_sep_memlist. 1: eassumption.
         - cbv [dexpr expr expr_body get]. eexists. subst l.
           rewrite map.get_put_diff by congruence.
           rewrite map.get_put_diff by congruence.
           rewrite map.get_put_diff by congruence.
           rewrite map.get_put_same. auto.
         - cbv [dexpr expr expr_body get]. eexists. subst l.
           rewrite map.get_put_diff by congruence.
           rewrite map.get_put_same. auto. }
    (*postcondition*)
    cbv [Morphisms.pointwise_relation Basics.impl].
    intros. fwd. cbn [list_map list_map_body]. split; [reflexivity|].
    split; [|reflexivity]. repeat rewrite byte_to_word_to_byte in H0p2.
    rewrite <- sep_assoc in H0p2. apply H0p2.
  Qed.

  Definition stackswap := func! (a, b) ~> (b, a) {
    stackalloc 4 as x;                          
    store1(x, a);
    stackalloc 4 as y;                          
    store1(y, b);
    swap(y, x);
    load1(a, x);
    load1(b, y)
  }.

  Check byte_to_word_to_byte.
  Instance spec_of_stackswap : spec_of "stackswap" :=
    fnspec! "stackswap" a b / abyte bbyte ~> B A,
    { requires t m := a = of_bytes [abyte] /\ b = of_bytes [bbyte];
      ensures t' m' := t' = t /\ m' = m /\ A = b /\ B = a }.

  Check load_one_of_sep_memlist.
  
  Lemma cmd_stackalloc e x n s t m l post :
    cmd e (cmd.stackalloc x n s) t m l post = (n mod bytes_per_word 32 = 0 /\
   (forall (a : word) (mStack mCombined : listmem),
    anybytes' a (BinIntDef.Z.to_nat n) mStack ->
    map.split mCombined m mStack ->
    dlet.dlet (map.put l x a)
      (fun l0 : locals =>
       cmd e s t mCombined l0
         (fun (t' : trace) (mCombined' : listmem) (l' : locals) =>
          exists m' mStack' : listmem,
            anybytes' a (BinIntDef.Z.to_nat n) mStack' /\
            map.split mCombined' m' mStack' /\ post t' m' l')))).
  Proof. reflexivity. Qed.

  Check cmd.call.
  Lemma cmd_call e args f rets t m l post :
    cmd e (cmd.call args f rets) t m l post = (exists args0 : list word,
     dexprs l rets args0 /\
     call e f t m args0
       (fun (t0 : trace) (m0 : listmem) (rets0 : list word) =>
        exists l' : locals,
          map.putmany_of_list_zip args rets0 l = Some l' /\ post t0 m0 l')).
  Proof. reflexivity. Qed.

  Lemma stackswap_ok : program_logic_goal_for_function! stackswap.
  Proof.
    repeat straightline. Fail unfold1_cmd_goal. (*why*)
    (*first stackalloc*)
    rewrite cmd_stackalloc. split; [reflexivity|]. intros.
    replace (BinIntDef.Z.to_nat 4) with 4%nat in H0 by reflexivity.
    cbv [dlet.dlet]. rewrite cmd_seq.
    destruct H0 as (bs&Hlenbs&H0).
    assert (mCombined =* array_byte a0 bs * (eq m)).
    { eexists. eexists. split. 1: apply map.split_comm. 1: eassumption. eauto. }
    destruct bs as [|? bs]; [discriminate Hlenbs|]. simpl in H2.
    rewrite sep_assoc in H2.
    (*first store*)
    eapply WeakestPreconditionProperties.Proper_cmd.
    2: { eapply store_one_of_sep_memlist. 1: eassumption.
         - cbv [dexpr expr expr_body get]. eexists. subst l.
           repeat (rewrite map.get_put_diff by congruence).
           rewrite map.get_put_same. auto.
         - cbv [dexpr expr expr_body get]. eexists. subst l.
           repeat (rewrite map.get_put_diff by congruence).
           rewrite map.get_put_same. auto. }
    cbv [Morphisms.pointwise_relation Basics.impl]. intros. fwd.
    subst a. rewrite byte_to_word_to_byte in H3p1.
    (*second stackalloc*)
    rewrite cmd_stackalloc. split; [reflexivity|]. intros.
    replace (BinIntDef.Z.to_nat 4) with 4%nat in H3 by reflexivity.
    cbv [dlet.dlet]. rewrite cmd_seq.
    destruct H3 as (bs2&Hlenbs2&H3).
    assert (mCombined0 =* array_byte a bs2 * (ptsto a0 abyte ⋆ (array_byte (word.add a0 (word.of_Z 1)) bs ⋆ eq m))).
    { eexists. eexists. split. 1: apply map.split_comm. 1: eassumption. eauto. }
    destruct bs2 as [|? bs2]; [discriminate Hlenbs2|]. simpl in H5.
    rewrite sep_assoc in H5.
    (*second store*)
    eapply WeakestPreconditionProperties.Proper_cmd.
    2: { eapply store_one_of_sep_memlist. 1: eassumption.
         - cbv [dexpr expr expr_body get]. eexists. subst l.
           repeat (rewrite map.get_put_diff by congruence).
           rewrite map.get_put_same. auto.
         - cbv [dexpr expr expr_body get]. eexists. subst l.
           repeat (rewrite map.get_put_diff by congruence).
           rewrite map.get_put_same. auto. }
    cbv [Morphisms.pointwise_relation Basics.impl]. intros. fwd.
    subst b. rewrite byte_to_word_to_byte in H6p1.
    (*function call*)
    rewrite cmd_seq. rewrite cmd_call. eexists. split.
    { cbv [dexprs list_map list_map_body expr expr_body get]. eexists. split.
      - rewrite map.get_put_same. reflexivity.
      - eexists. split.
        + rewrite map.get_put_diff by congruence. rewrite map.get_put_same. reflexivity.
        + reflexivity. }
    clear H5. clear H2. clear H3p1. rewrite <- sep_assoc in H6p1.
    rewrite <- sep_assoc in H6p1. erewrite idk in H6p1.
    2: { intros. instantiate (1 := (ptsto _ _ * ptsto _ _ * _)%sep).
         erewrite idk.
         2: { intros. instantiate (1 := (_ * ptsto _ _)%sep). apply sep_comm. }
         rewrite sep_assoc. rewrite sep_comm. reflexivity. }
    rewrite sep_assoc in H6p1.
    straightline_call. 1: eassumption. fwd. eexists. split; [reflexivity|].
    (*first load*)
    rewrite cmd_seq. clear H6p1.
    erewrite idk in H2p1.
    2: { intros. instantiate (1 := (ptsto _ _ * ptsto _ _)%sep). apply sep_comm. }
    rewrite sep_assoc in H2p1.
    eapply WeakestPreconditionProperties.Proper_cmd.
    2: { eapply load_one_of_sep_memlist. 1: eassumption.
         - cbv [dexpr expr expr_body get]. eexists. subst l.
           repeat (rewrite map.get_put_diff by congruence).
           rewrite map.get_put_same. auto. }
    cbv [Morphisms.pointwise_relation Basics.impl]. intros. fwd.
    (*second load*)
    rewrite <- sep_assoc in H2p1.
    erewrite idk in H2p1.
    2: { intros. instantiate (1 := (ptsto _ _ * ptsto _ _)%sep). apply sep_comm. }
    rewrite sep_assoc in H2p1.
    eapply WeakestPreconditionProperties.Proper_cmd.
    2: { eapply load_one_of_sep_memlist. 1: eassumption.
         - cbv [dexpr expr expr_body get]. eexists. subst l.
           repeat (rewrite map.get_put_diff by congruence).
           rewrite map.get_put_same. auto. }
    cbv [Morphisms.pointwise_relation Basics.impl]. intros. fwd.
    (*first stackdealloc*)
    do 2 rewrite <- sep_assoc in H2p1. erewrite idk in H2p1.
    2: { intros. instantiate (1 := (array_byte _ _ * ptsto _ _)%sep). rewrite sep_assoc.
         rewrite sep_comm. erewrite idk.
         2: { intros. instantiate (1 := (_ * ptsto _ _)%sep). apply sep_comm. }
         rewrite sep_comm. rewrite <- sep_assoc. instantiate (3 := (abyte :: bs2)).
         simpl. reflexivity. }
    rewrite sep_assoc in H2p1.
    destruct H2p1 as (mStack' & m' & Hsplit & HmStack' & Hm').
    exists m', mStack'. split.
    { eexists. split; [|eassumption]. simpl in Hlenbs2. simpl. lia. }
    split.
    { apply map.split_comm. assumption. }
    (*second stackdealloc*)
    rewrite <- sep_assoc in Hm'.
    eassert (array_byte a0 (bbyte :: bs) = _) as arr.
    { simpl. reflexivity. }
    rewrite <- arr in Hm'. clear arr.
    destruct Hm' as (mStack'0 & m'0 & Hsplit0 & HmStack'0 & Hm'0).
    exists m'0, mStack'0. split.
    { eexists. split; [|eassumption]. simpl in Hlenbs. simpl. lia. }
    split.
    { apply map.split_comm. assumption. }
    (*postcondition*)
    cbv [list_map list_map_body get]. eexists. split.
    { repeat (rewrite map.get_put_diff by congruence). rewrite map.get_put_same. auto. }
    eexists. split.
    { repeat (rewrite map.get_put_diff by congruence). rewrite map.get_put_same. auto. }
    eexists. eexists. eauto.
  Qed.
  Print Assumptions stackswap_ok.

(*
Section Variables:
    word_ok : word.ok word
    word : Interface.word 32
    mem_ok : map.ok mem
    mem : map.map word (Init.Byte.byte : Type)
    locals_ok : map.ok locals
    locals : map.map String.string word
    listmem_ok : map.ok listmem
    listmem : map.map (word * nat) (Init.Byte.byte : Type)
    ext_spec_ok : ext_spec.ok ext_spec
    ext_spec : ExtSpec
    BW : Bitwidth 32

Axioms:
    wordnat_eqb_spec :
        forall (width : Z) (BW : Bitwidth width) (word : Interface.word width)
        (listmem : map.map (word * nat) (Init.Byte.byte : Type)),
        word.ok word -> EqDecider wordnat_eqb
    wordnat_eqb :
        forall width : Z,
        Bitwidth width ->
        forall word : Interface.word width,
        map.map (word * nat) (Init.Byte.byte : Type) -> word * nat -> word * nat -> bool
*)
End WithParameters.
