Require Import coqutil.Datatypes.PrimitivePair coqutil.Datatypes.HList coqutil.dlet.
Require Import Coq.Classes.Morphisms BinIntDef.
Require Import coqutil.Macros.unique coqutil.Map.Interface coqutil.Word.Interface. Import map.
Require Import coqutil.Word.Bitwidth.
Require Import coqutil.Map.Properties.
Require Import coqutil.Tactics.destr.
From bedrock2 Require Import Map.Separation Map.SeparationLogic.
From bedrock2 Require Import Syntax Semantics Markers.
From bedrock2 Require Import WeakestPrecondition WeakestPreconditionProperties.

Section Loops.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word Byte.byte}.
  Context {locals: map.map String.string word}.
  Context {env: map.map String.string (list String.string * list String.string * Syntax.cmd)}.
  Context {ext_spec: ExtSpec}.
  Context {word_ok : word.ok word} {mem_ok : map.ok mem}.
  Context {locals_ok : map.ok locals}.
  Context {env_ok : map.ok env}.
  Context {ext_spec_ok : Semantics.ext_spec.ok ext_spec}.

  Context {functions : list (String.string * (list String.string * list String.string * Syntax.cmd))}.
  Let call := WeakestPrecondition.call functions.
  Lemma tailrec_localsmap_1ghost
    {e c t} {m: mem} {l} {a} {post : io_trace -> mem -> locals -> abstract_trace -> Prop}
    {measure: Type} {Ghost: Type}
    (P Q: measure -> Ghost -> io_trace -> mem -> locals -> abstract_trace -> Prop)
    (lt: measure -> measure -> Prop)
    (Hwf: well_founded lt)
    (v0: measure) (g0: Ghost)
    (Hpre: P v0 g0 t m l a)
    (Hbody: forall v g t m l a,
      P v g t m l a ->
      exists br a', dexpr m l a e br (cons_branch (negb (Z.eqb (word.unsigned br) 0)%Z) a') (* why was dexpr not written here originally? *) /\
      (word.unsigned br <> 0%Z -> cmd call c t m l a'
        (fun t' m' l' a'' => exists v' g',
          P v' g' t' m' l' a'' /\
          lt v' v /\
          (forall t'' m'' l'' a''', Q v' g' t'' m'' l'' a''' -> Q v g t'' m'' l'' a'''))) /\
      (word.unsigned br = 0%Z -> Q v g t m l a'))
    (Hpost: forall t m l a, Q v0 g0 t m l a -> post t m l a)
    : cmd call (cmd.while e c) t m l a post.
  Proof.
    eexists measure, lt, (fun v t m l a =>
      exists g, P v g t m l a /\ forall t'' m'' l'' a''', Q v g t'' m'' l'' a''' -> Q v0 g0 t'' m'' l'' a''').
    split; [assumption|].
    split; [solve[eauto]|].
    intros vi ti mi li ai (gi & HPi & HQimpl).
    specialize (Hbody vi gi ti mi li ai HPi).
    destruct Hbody as (br & a' & ? & Hbody). exists br, a'.
    split; [assumption|].
    destruct Hbody as (Htrue & Hfalse). split; intros Hbr;
      [pose proof(Htrue Hbr)as Hpc|pose proof(Hfalse Hbr)as Hpc]; clear Hbr Htrue Hfalse.
    { eapply Proper_cmd; [assumption..| | |eapply Hpc].
      { eapply Proper_call; eauto (*firstorder idtac takes a long time here*). }
      intros tj mj lj aj (vj& gj & HPj & Hlt & Qji); eauto 7. }
    { eauto. }
  Qed.

  Lemma tailrec_localsmap_1ghost_parameterized_finalpost
    {e c rest t} {m: mem} {l} {a}
    {measure: Type} {Ghost: Type}
    (P Q: measure -> Ghost -> io_trace -> mem -> locals -> abstract_trace -> Prop)
    (lt: measure -> measure -> Prop)
    (Hwf: well_founded lt)
    (v0: measure) (g0: Ghost)
    (Hpre: P v0 g0 t m l a)
    (Hbody: forall v g t m l a,
      P v g t m l a ->
      exists br a', dexpr m l a e br (cons_branch (negb (Z.eqb (word.unsigned br) 0)) a') /\
      (word.unsigned br <> 0%Z -> cmd call c t m l a'
        (fun t' m' l' a'' => exists v' g',
          P v' g' t' m' l' a'' /\
          lt v' v /\
          (forall t'' m'' l'' a''', Q v' g' t'' m'' l'' a''' -> Q v g t'' m'' l'' a'''))) /\
      (word.unsigned br = 0%Z -> cmd call rest t m l a' (Q v g)))
    : cmd call (cmd.seq (cmd.while e c) rest) t m l a (Q v0 g0).
  Proof.
    cbn. eapply @tailrec_localsmap_1ghost with
      (Q := fun v g t m l a => cmd call rest t m l a (Q v g))
      (post := fun t m l a => cmd call rest t m l a (Q v0 g0)).
    1: eassumption.
    1: exact Hpre.
    2: intros *; exact id.
    intros vi gi ti mi li ai HPi.
    specialize (Hbody vi gi ti mi li ai HPi).
    destruct Hbody as (br & a' & ? & Hbody). exists br, a'; split; [assumption|].
    destruct Hbody as (Htrue & Hfalse). split; intros Hbr;
      [pose proof(Htrue Hbr)as Hpc|pose proof(Hfalse Hbr)as Hpc]; clear Hbr Htrue Hfalse.
    { eapply Proper_cmd; [assumption..| | |eapply Hpc].
      { eapply Proper_call; eauto(*firstorder idtac takes a long time here*). }
      intros tj mj lj aj (vj& gj & HPj & Hlt & Qji). do 2 eexists.
      split. 1: eassumption. split. 1: assumption.
      intros.
      eapply Proper_cmd; [assumption..| | | ].
      3: eassumption.
      { eapply Proper_call; eauto(*firstorder idtac takes a long time here*). }
      intros tk mk lk ak HH. eapply Qji. assumption. }
    eapply Hpc.
  Qed.

  (* marking logical connectives with the source file they were used in for limiting unfolding *)
  Local Notation "A /\ B" := (Markers.split (A /\ B)).
  Local Notation "A /\ B" := (Markers.split (A /\ B)) : type_scope.

  (* shallow reflection for resolving map accesses during symbolic execution *)
  (* each lemma below is duplicated for various levels of use of this trick *)
  Definition reconstruct (variables:list String.string) (values:tuple word (length variables)) : locals :=
    map.putmany_of_tuple (tuple.of_list variables) values map.empty.
  Fixpoint gather (variables : list String.string) (l : locals) : option (locals *  tuple word (length variables)) :=
    match variables with
    | nil => Some (l, tt)
    | cons x xs' =>
      match map.get l x with
      | None => None
      | Some v =>
        match gather xs' (map.remove l x) with
        | None => None
        | Some (l, vs') => Some (l, (pair.mk v vs'))
        end
      end
    end.

  Lemma putmany_gather ks vs m me (H : gather ks m = Some (me, vs)) :
    map.putmany_of_tuple (tuple.of_list ks) vs me = m.
  Proof.
    revert H; revert me; revert m; revert vs; induction ks; cbn [gather map.putmany_of_list]; intros.
    { inversion H; subst. exact eq_refl. }
    repeat match type of H with context[match ?x with _ => _ end] => destruct x eqn:? end;
      repeat (match goal with H : _ |- _ => eapply IHks in H end); inversion H; subst; clear H.
    cbn [map.putmany_of_tuple tuple.of_list length].
    match goal with H : _ |- _ => rewrite H; clear H end.
    assert (map.get m a = Some r -> put (remove m a) a r = m). {
      intro A.
      apply map_ext.
      intro k.
      erewrite map.get_put_dec.
      destr (String.eqb a k); try congruence.
      rewrite map.get_remove_diff; congruence.
    }
    auto.
  Qed.

  Definition enforce (variables : list String.string) (values:tuple word (length variables)) (l:locals) : Prop :=
    match gather variables l with
    | None => False
    | Some (remaining, r) => values = r /\ remaining = map.empty
    end.
  Lemma reconstruct_enforce variables ll lm (H : enforce variables ll lm) : lm = reconstruct variables ll.
    progress cbv [enforce] in H.
    repeat match type of H with context[match ?x with _ => _ end] => destruct x eqn:? end;
      destruct H; subst.
    symmetry. eapply putmany_gather. assumption.
  Qed.

  Lemma hlist_forall_foralls: forall (argts : polymorphic_list.list Type) (P : hlist argts -> Prop), (forall x : hlist argts, P x) -> hlist.foralls P.
  Proof. induction argts; cbn; auto. Qed.

  Import pair.

  Lemma while_localsmap
    {e c t l a} {m : mem}
    {measure : Type} (invariant:_->_->_->_->_-> Prop)
    {lt} (Hwf : well_founded lt) (v0 : measure)
    {post : _->_->_->_-> Prop}
    (Hpre : invariant v0 t m l a)
    (Hbody : forall v t m l a,
      invariant v t m l a ->
      exists br a', dexpr m l a e br (cons_branch (negb (Z.eqb (word.unsigned br) 0)) a') /\
         (word.unsigned br <> 0 ->
          cmd call c t m l a' (fun t m l a => exists v', invariant v' t m l a /\ lt v' v)) /\
         (word.unsigned br = 0 -> post t m l a'))
    : cmd call (cmd.while e c) t m l a post.
  Proof.
    eexists measure, lt, invariant.
    split. 1: exact Hwf.
    split. 1: eauto.
    exact Hbody.
  Qed.

  Lemma while
    {e c t l a} {m : mem}
    (variables : list String.string)
    {localstuple : tuple word (length variables)}
    {measure : Type} (invariant:_->_->_-> (ufunc word (length variables) (_->Prop)))
    {lt} (Hwf : well_founded lt) (v0 : measure)
    {post : _->_->_->_-> Prop}
    (Pl : enforce variables localstuple l)
    (Hpre : tuple.apply (invariant v0 t m) localstuple a)
    (Hbody : forall v t m a, tuple.foralls (fun localstuple =>
      (tuple.apply (invariant v t m) localstuple) a ->
      let l := reconstruct variables localstuple in
      exists br a', dexpr m l a e br (cons_branch (negb (Z.eqb (word.unsigned br) 0)) a') /\
         (word.unsigned br <> 0 ->
          cmd call c t m l a' (fun t m l a =>
            Markers.unique (Markers.left (tuple.existss (fun localstuple =>
              enforce variables localstuple l /\
              Markers.right (Markers.unique (exists v',
                tuple.apply (invariant v' t m) localstuple a /\ lt v' v))))))) /\
         (word.unsigned br = 0 -> post t m l a')))
    : cmd call (cmd.while e c) t m l a post.
  Proof.
    eapply (while_localsmap (fun v t m l a =>
      exists localstuple, enforce variables localstuple l /\
                          tuple.apply (invariant v t m) localstuple a));
      unfold Markers.split; eauto.
    intros vi ti mi li ai (?&X&Y).
    specialize (Hbody vi ti mi).
    eapply hlist.foralls_forall in Hbody.
    specialize (Hbody Y).
    rewrite <-(reconstruct_enforce _ _ _ X) in Hbody.
    destruct Hbody as (br & a' & Cond & Again & Done).
    exists br. exists a'. split; [exact Cond|]. split; [|exact Done].
    intro NE. specialize (Again NE).
    eapply Proper_cmd; [assumption..| eapply Proper_call; assumption| |eapply Again].
    cbv [Morphisms.pointwise_relation Basics.impl Markers.right Markers.unique Markers.left] in *.
    intros t' m' l' a'' Ex.
    eapply hlist.existss_exists in Ex. cbv beta in Ex. destruct Ex as (ls & E & v' & Inv' & LT).
    eauto.
  Qed.

  Lemma tailrec
    {e c t localsmap a} {m : mem}
    (ghosttypes : polymorphic_list.list Type)
    (variables : list String.string)
    {l0 : tuple word (length variables)}
    {Pl : enforce variables l0 localsmap}
    {post : io_trace->_->_->_-> Prop}
    {measure : Type} (spec:_->HList.arrows ghosttypes (_->_->ufunc word (length variables) (_->Prop*(_->_->ufunc word (length variables) (_->Prop))))) lt
    (Hwf : well_founded lt)
    (v0 : measure)
    : hlist.foralls (fun (g0 : hlist ghosttypes) => forall
    (Hpre : (tuple.apply (hlist.apply (spec v0) g0 t m) l0 a).(1))
    (Hbody : forall v, hlist.foralls (fun g => forall t m, tuple.foralls (fun l =>
      forall a,
      @dlet _ (fun _ => Prop) (reconstruct variables l) (fun localsmap : locals =>
      match tuple.apply (hlist.apply (spec v) g t m) l a with S_ =>
      S_.(1) ->
      Markers.unique (Markers.left (exists br a', dexpr m localsmap a e br (cons_branch (negb (Z.eqb (word.unsigned br) 0)) a') /\ Markers.right (
      (word.unsigned br <> 0%Z -> cmd call c t m localsmap a'
        (fun t' m' localsmap' a'' =>
          Markers.unique (Markers.left (hlist.existss (fun l' => enforce variables l' localsmap' /\ Markers.right (
          Markers.unique (Markers.left (hlist.existss (fun g' => exists v',
          match tuple.apply (hlist.apply (spec v') g' t' m') l' a'' with S' =>
          S'.(1) /\ Markers.right (
            lt v' v /\
            forall T M, hlist.foralls (fun L => forall A, tuple.apply (S'.(2) T M) L A -> tuple.apply (S_.(2) T M) L A)) end))))))))) /\
      (word.unsigned br = 0%Z -> tuple.apply (S_.(2) t m) l a')))) end))))
    (Hpost : match (tuple.apply (hlist.apply (spec v0) g0 t m) l0 a).(2) with Q0 => forall t m, hlist.foralls (fun l => forall a, tuple.apply (Q0 t m) l a -> post t m (reconstruct variables l) a)end)
    , cmd call (cmd.while e c) t m localsmap a post).
  Proof.
    eapply hlist_forall_foralls; intros g0 **.
    eexists measure, lt, (fun vi ti mi localsmapi ai =>
      exists gi li, localsmapi = reconstruct variables li /\
      match tuple.apply (hlist.apply (spec vi) gi ti mi) li ai with S_ =>
      S_.(1) /\ forall T M L A, tuple.apply (S_.(2) T M) L A ->
        tuple.apply ((tuple.apply (hlist.apply (spec v0) g0 t m) l0 a).(2) T M) L A end).
    cbv [Markers.split Markers.left Markers.right] in *.
    split; [assumption|].
    split. { exists v0, g0, l0. split. 1: eapply reconstruct_enforce; eassumption. split; eauto. }
    intros vi ti mi lmapi ai (gi&?&?&?&Qi); subst.
    Check (hlist.foralls_forall (hlist.foralls_forall (Hbody vi) gi ti mi) _ _).
    Check (hlist.foralls_forall (Hbody vi) gi ti mi).
    destruct (hlist.foralls_forall (hlist.foralls_forall (Hbody vi) gi ti mi) _ _ H0) as (br&a'&?&X).
    exists br. exists a'. split; [assumption|]. destruct X as (Htrue&Hfalse). split; intros Hbr;
      [pose proof(Htrue Hbr)as Hpc|pose proof(Hfalse Hbr)as Hpc]; clear Hbr Htrue Hfalse.
    { eapply Proper_cmd; [assumption..| | |eapply Hpc].
      { eapply Proper_call; eauto(*firstorder idtac is very slow here*). }
      intros tj mj lmapj aj Hlj; eapply hlist.existss_exists in Hlj.
      destruct Hlj as (lj&Elj&HE); eapply reconstruct_enforce in Elj; subst lmapj.
      eapply hlist.existss_exists in HE. destruct HE as (l&?&?&?&HR).
      pose proof fun T M => hlist.foralls_forall (HR T M); clear HR.
      eauto 9. }
    { pose proof fun t m => hlist.foralls_forall (Hpost t m); clear Hpost; eauto. }
  Qed.

  Lemma tailrec_localsmap
    {e c t} {m : mem} {l} {a} {post : _->_->_->_-> Prop}
    {measure : Type} (spec:_->_->_->_->_->(Prop*(_->_->_->_-> Prop))) lt
    (Hwf : well_founded lt)
    (v0 : measure) (P0 := (spec v0 t m l a).(1)) (Hpre : P0)
    (Q0 := (spec v0 t m l a).(2))
    (Hbody : forall v t m l a,
      let S := spec v t m l a in let (P, Q) := S in
      P ->
      exists br a', dexpr m l a e br (cons_branch (negb (Z.eqb (word.unsigned br) 0)) a') /\
      (word.unsigned br <> 0%Z -> cmd call c t m l a'
        (fun t' m' l' a'' => exists v',
          let S' := spec v' t' m' l' a'' in let '(P', Q') := S' in
          P' /\
          lt v' v /\
          forall T M L A, Q' T M L A -> Q T M L A)) /\
      (word.unsigned br = 0%Z -> Q t m l a'))
    (Hpost : forall t m l a, Q0 t m l a -> post t m l a)
    : cmd call (cmd.while e c) t m l a post.
  Proof.
    eexists measure, lt, (fun v t m l a =>
      let S := spec v t m l a in let '(P, Q) := S in
      P /\ forall T M L A, Q T M L A -> Q0 T M L A).
    split; [assumption|].
    cbv [Markers.split] in *.
    split; [solve[eauto]|].
    intros vi ti mi li ai (?&Qi).
    destruct (Hbody _ _ _ _ _ ltac:(eassumption)) as (br&a'&?&X); exists br; exists a'; split; [assumption|].
    destruct X as (Htrue&Hfalse). split; intros Hbr;
      [pose proof(Htrue Hbr)as Hpc|pose proof(Hfalse Hbr)as Hpc]; clear Hbr Htrue Hfalse.
    { eapply Proper_cmd; [assumption..| | |eapply Hpc].
      { eapply Proper_call; eauto (*firstorder idtac is very slow*). }
      intros tj mj lj aj (vj&dP&?&dQ); eauto 9. }
    { eauto. }
  Qed.

  Definition with_bottom {T} R (x y : option T) :=
    match x, y with
    | None, Some _ => True
    | Some x, Some y => R x y
    | _, _ => False
    end.
  Lemma well_founded_with_bottom {T} R (H : @well_founded T R) : well_founded (with_bottom R).
  Proof.
    intros [x|]; cycle 1.
    { constructor; intros [] HX; cbv [with_bottom] in HX; contradiction. }
    pattern x. revert x. eapply (@well_founded_ind _ _ H). intros.
    constructor. intros [y|] pf; eauto.
    constructor. intros [] [].
  Qed.


  Lemma atleastonce_localsmap
    {e c t} {m : mem} {l} {a} {post : _->_->_->_-> Prop}
    {measure : Type} (invariant:_->_->_->_->_->Prop) lt
    (Hwf : well_founded lt)
    (v0 : measure)
    (Henter : exists br a', dexpr m l a e br (cons_branch (negb (Z.eqb (word.unsigned br) 0)) a') /\
                              (word.unsigned br = 0%Z -> post t m l a') /\
    (word.unsigned br <> 0%Z -> invariant v0 t m l a'))
    (*(Hpre : invariant v0 t m l) this is useless now. I replace it by making  
      Henter bigger *)
    (Hbody : forall v t m l a, invariant v t m l a ->
       cmd call c t m l a (fun t m l a =>
         exists br a', dexpr m l a e br (cons_branch (negb (Z.eqb (word.unsigned br) 0)) a') /\
         (word.unsigned br <> 0 -> exists v', invariant v' t m l a' /\ lt v' v) /\
         (word.unsigned br =  0 -> post t m l a')))
    : cmd call (cmd.while e c) t m l a post.
  Proof.
    eexists (option measure), (with_bottom lt), (fun ov t m l a =>
      exists br a', dexpr m l a e br (cons_branch (negb (Z.eqb (word.unsigned br) 0)) a') /\
      ((word.unsigned br <> 0 -> exists v, ov = Some v /\ invariant v t m l a') /\
      (word.unsigned br =  0 -> ov = None /\ post t m l a'))).
    split; auto using well_founded_with_bottom; []. split.
    { destruct Henter as [br [a' [He [Henterfalse Hentertrue]]]].
      destruct (BinInt.Z.eq_dec (word.unsigned br) 0).
      { exists None, br, a'; split; trivial.
        split; intros; try contradiction; split; eauto. }
      { exists (Some v0), br, a'.
        split; trivial; []; split; try contradiction.
        exists v0; split; auto. } }
    intros vi ti mi li ai (br&a'&Ebr&Hcontinue&Hexit).
    eexists. eexists. split; [eassumption|]; split.
    { intros Hc; destruct (Hcontinue Hc) as (v&?&Hinv); subst.
      eapply Proper_cmd; [assumption..| | |eapply Hbody; eassumption]; [eapply Proper_call; assumption|].
      intros t' m' l' a'' (br'&a'2&Ebr'&Hinv'&Hpost').
      destruct (BinInt.Z.eq_dec (word.unsigned br') 0).
      { exists None; split; try constructor.
        exists br'; exists a'2; split; trivial; [].
        split; intros; try contradiction.
        split; eauto. }
      { destruct (Hinv' ltac:(trivial)) as (v'&inv'&ltv'v).
        exists (Some v'); split; trivial. (* NOTE: this [trivial] simpl-reduces [with_bottom] *)
        exists br'; exists a'2; split; trivial.
        split; intros; try contradiction.
        eexists; split; eauto. } }
    eapply Hexit.
  Qed.

  Lemma tailrec_earlyout_localsmap
    {e c t} {m : mem} {l} {a} {post : _->_->_->_-> Prop}
    {measure : Type} (spec:_->_->_->_->_->(Prop*(_->_->_->_-> Prop))) lt
    (Hwf : well_founded lt)
    (v0 : measure) (P0 := (spec v0 t m l a).(1)) (Hpre : P0)
    (Q0 := (spec v0 t m l a).(2))
    (Hbody : forall v t m l a,
      let S := spec v t m l a in let (P, Q) := S in
      P ->
      exists br a', dexpr m l a e br (cons_branch (negb (Z.eqb (word.unsigned br) 0)) a') /\
      (word.unsigned br <> 0%Z -> cmd call c t m l a'
        (fun t' m' l' a'' =>
          (exists br a''', dexpr m' l' a'' e br (cons_branch false a''') /\ word.unsigned br = 0 /\ Q t' m' l' a''') \/
          exists v', let S' := spec v' t' m' l' a'' in let '(P', Q') := S' in
          P' /\
          lt v' v /\
          forall T M L A, Q' T M L A -> Q T M L A)) /\
      (word.unsigned br = 0%Z -> Q t m l a'))
    (Hpost : forall t m l a, Q0 t m l a -> post t m l a)
    : cmd call (cmd.while e c) t m l a post.
  Proof.
    eexists (option measure), (with_bottom lt), (fun v t m l a =>
      match v with
      | None => exists br a', dexpr m l a e br (cons_branch false a') /\ word.unsigned br = 0 /\ Q0 t m l a'
      | Some v =>
          let S := spec v t m l a in let '(P, Q) := S in
          P /\ forall T M L A, Q T M L A -> Q0 T M L A
      end).
    split; auto using well_founded_with_bottom; []; cbv [Markers.split] in *.
    split.
    { exists (Some v0); eauto. }
    intros [vi|] ti mi li ai inv_i; [destruct inv_i as (?&Qi)|destruct inv_i as (br&a'&Hebr&Hbr0&HQ)].
    { destruct (Hbody _ _ _ _ _ ltac:(eassumption)) as (br&a'&?&X); exists br, a'; split; [assumption|].
      destruct X as (Htrue&Hfalse). split; intros Hbr;
        [pose proof(Htrue Hbr)as Hpc|pose proof(Hfalse Hbr)as Hpc]; eauto.
      eapply Proper_cmd; [assumption..| | |eapply Hpc].
      { eapply Proper_call; eauto (*firstorder idtac is very slow here*). }
      intros tj mj lj aj [(br'&a''&Hbr'&Hz&HQ)|(vj&dP&?&dQ)];
      [exists None | exists (Some vj)]; cbn [with_bottom]; eauto 9. }
    exists br.
    repeat esplit || eauto || intros.
    { rewrite Hbr0. assumption. }
    { contradiction. }
  Qed.

  Lemma tailrec_earlyout
    {e c t localsmap a} {m : mem}
    (ghosttypes : polymorphic_list.list Type)
    (variables : list String.string)
    {l0 : tuple word (length variables)}
    {Pl : enforce variables l0 localsmap}
    {post : _->_->_->_-> Prop}
    {measure : Type} (spec:_->HList.arrows ghosttypes (_->_->ufunc word (length variables) (_->Prop*(_->_->ufunc word (length variables) (_->Prop))))) lt
    (Hwf : well_founded lt)
    (v0 : measure)
    : hlist.foralls (fun (g0 : hlist ghosttypes) => forall
    (Hpre : (tuple.apply (hlist.apply (spec v0) g0 t m) l0 a).(1))
    (Hbody : forall v, hlist.foralls (fun g => forall t m, tuple.foralls (fun l =>
      forall a,
      @dlet _ (fun _ => Prop) (reconstruct variables l) (fun localsmap : locals =>
      match tuple.apply (hlist.apply (spec v) g t m) l a with S_ =>
      S_.(1) ->
      Markers.unique (Markers.left (exists br a', dexpr m localsmap a e br (cons_branch (negb (Z.eqb (word.unsigned br) 0)) a') /\ Markers.right (
      (word.unsigned br <> 0%Z -> cmd call c t m localsmap a'
        (fun t' m' localsmap' a'' =>
          Markers.unique (Markers.left (hlist.existss (fun l' => enforce variables l' localsmap' /\ Markers.right (
          Markers.unique (Markers.left (exists br' a''', dexpr m' localsmap' a'' e br' (cons_branch false a''') /\ Markers.right (word.unsigned br'= 0 /\ tuple.apply (S_.(2) t' m') l' a''') ) ) \/
          Markers.unique (Markers.left (hlist.existss (fun g' => exists v',
          match tuple.apply (hlist.apply (spec v') g' t' m') l' a'' with S' =>
          S'.(1) /\ Markers.right (
            lt v' v /\
            forall T M, hlist.foralls (fun L => forall A, tuple.apply (S'.(2) T M) L A -> tuple.apply (S_.(2) T M) L A)) end))))))))) /\
      (word.unsigned br = 0%Z -> tuple.apply (S_.(2) t m) l a'))))end))))
    (Hpost : match (tuple.apply (hlist.apply (spec v0) g0 t m) l0 a).(2) with Q0 => forall t m, hlist.foralls (fun l => forall a, tuple.apply (Q0 t m) l a -> post t m (reconstruct variables l) a)end)
    , cmd call (cmd.while e c) t m localsmap a post).
  Proof.
    eapply hlist_forall_foralls; intros g0 **.
    eexists (option measure), (with_bottom lt), (fun vi ti mi localsmapi ai =>
      exists li, localsmapi = reconstruct variables li /\
                   match vi with
                   | None => exists br ai', dexpr mi localsmapi ai e br (cons_branch false ai') /\ word.unsigned br = 0 /\ tuple.apply ((tuple.apply (hlist.apply (spec v0) g0 t m) l0 a).(2) ti mi) li ai'
                   | Some vi => exists gi,
                       match tuple.apply (hlist.apply (spec vi) gi ti mi) li ai with
                       | S_ => S_.(1) /\ forall T M L A, tuple.apply (S_.(2) T M) L A -> tuple.apply ((tuple.apply (hlist.apply (spec v0) g0 t m) l0 a).(2) T M) L A end
                   end).
    cbv [Markers.unique Markers.split Markers.left Markers.right] in *.
    split; eauto using well_founded_with_bottom.
    split. { exists (Some v0), l0. split. 1: eapply reconstruct_enforce; eassumption. exists g0; split; eauto. }
    intros [vi|] ti mi lmapi ai.
    2: { intros (ld&Hd&br&ai'&Hbr&Hz&Hdone).
         eexists. eexists. split; eauto.
         { rewrite Hz. eauto. }
      split; intros; try contradiction.
      subst. eapply (hlist.foralls_forall (Hpost ti mi) _ _ Hdone). }
    intros (?&?&gi&?&Qi); subst.
    destruct (hlist.foralls_forall (hlist.foralls_forall (Hbody vi) gi ti mi) _ _ ltac:(eassumption)) as (br&a'&?&X).
    exists br. exists a'. split; [assumption|]. destruct X as (Htrue&Hfalse). split; intros Hbr;
      [pose proof(Htrue Hbr)as Hpc|pose proof(Hfalse Hbr)as Hpc]; clear Hbr Htrue Hfalse.
    { eapply Proper_cmd; [assumption..| | |eapply Hpc].
      { eapply Proper_call; eauto (*firstorder idtac is very slow here*). }
      intros tj mj lmapj aj Hlj; eapply hlist.existss_exists in Hlj.
      destruct Hlj as (lj&Elj&HE); eapply reconstruct_enforce in Elj; subst lmapj.
      destruct HE as [(br'&a'''&Hevalr'&Hz'&Hdone)|HE].
      { exists None; cbn. eauto 9. }
      { eapply hlist.existss_exists in HE. destruct HE as (l&?&?&?&HR).
        pose proof fun T M => hlist.foralls_forall (HR T M); clear HR.
        eexists (Some _); eauto 9. } }
    { pose proof fun t m => hlist.foralls_forall (Hpost t m); clear Hpost; eauto. }
  Qed.


  Lemma atleastonce
    {e c t l a} {m : mem}
    (variables : list String.string)
    {localstuple : tuple word (length variables)}
    {Pl : enforce variables localstuple l}
    {measure : Type} (invariant:_->_->_->ufunc word (length variables) (_->Prop))
    lt (Hwf : well_founded lt)
    {post : _->_->_->_-> Prop}
    (v0 : measure)
    (Henter : exists br a', dexpr m l a e br (cons_branch (negb (Z.eqb (word.unsigned br) 0)) a') /\
                              (word.unsigned br = 0%Z -> post t m l a') /\
                              (word.unsigned br <> 0%Z -> tuple.apply (invariant v0 t m) localstuple a'))
    (*(Hpre : tuple.apply (invariant v0 t m) localstuple) this is useless, just like in atleastone_localsmap *)
    (Hbody : forall v t m, tuple.foralls (fun localstuple => forall a,
      tuple.apply (invariant v t m) localstuple a ->
       cmd call c t m (reconstruct variables localstuple) a (fun t m l a =>
         exists br a', dexpr m l a e br (cons_branch (negb (Z.eqb (word.unsigned br) 0)) a') /\
                         (word.unsigned br <> 0 ->
                          Markers.unique (Markers.left (tuple.existss (fun localstuple => enforce variables localstuple l /\
                                                                                            Markers.right (Markers.unique (exists v', tuple.apply (invariant v' t m) localstuple a' /\ lt v' v)))))) /\
                         (word.unsigned br =  0 -> post t m l a'))))
    : cmd call (cmd.while e c) t m l a post.
  Proof.
    destruct Henter as [br [a' [Henter [Hentertrue Henterfalse]]]].
    eapply (atleastonce_localsmap (fun v t m l a => exists localstuple, Logic.and (enforce variables localstuple l) (tuple.apply (invariant v t m) localstuple a))); eauto.
    { eexists. eexists. split; eauto. split; eauto. }
    intros vi ti mi li ai (?&X&Y).
    specialize (Hbody vi ti mi).
    eapply hlist.foralls_forall in Hbody.
    specialize (Hbody ai Y).
    rewrite <-(reconstruct_enforce _ _ _ X) in Hbody.
    eapply Proper_cmd; [assumption..|eapply Proper_call; assumption| |eapply Hbody].
    intros t' m' l' a'' (?&?&?&HH&?).
    eexists. eexists. split; eauto.
    split; intros; eauto.
    specialize (HH ltac:(eauto)).
    eapply hlist.existss_exists in HH; destruct HH as (?&?&?&?&?).
    eexists; split; eauto.
  Qed.

  Lemma while_zero_iterations {e c t l a} {m : mem} {post : _->_->_->_-> Prop}
    (HCondPost: exists a', dexpr m l a e (word.of_Z 0) (cons_branch false a') /\ post t m l a')
    (*(HPost: post t m l) no good :( *)
    : cmd call (cmd.while e c) t m l a post.
  Proof.
    destruct HCondPost as [a' [HCond HPost]].
    eapply (while_localsmap (fun n t' m' l' a' => t' = t /\ m' = m /\ l' = l /\ a' = a) (PeanoNat.Nat.lt_wf 0) 0%nat).
    1: unfold split; auto. intros *. intros (? & ? & ? & ?). subst.
    exists (word.of_Z 0). rewrite Properties.word.unsigned_of_Z_0.
    eexists. split. 1: exact HCond.
    split; intros; try congruence.
  Qed.


  (* Bedrock-style loop rule *)
  Local Open Scope sep_scope.
  Local Infix "*" := Separation.sep : type_scope.
  Local Infix "==>" := Lift1Prop.impl1.

  Lemma tailrec_sep
    e c t (m : mem) l a (post : _->_->_->_-> Prop)
    {measure : Type} P Q lt (Hwf : well_founded lt) (v0 : measure) R0
    (Hpre : (P v0 t l a * R0) m)
    (Hbody : forall v t m l a R, (P v t l a * R) m ->
      exists br a', dexpr m l a e br (cons_branch (negb (Z.eqb (word.unsigned br) 0)) a') /\
      (word.unsigned br <> 0%Z -> cmd call c t m l a'
        (fun t' m' l' a'' => exists v' dR, (P v' t' l' a'' * (R * dR)) m' /\
          lt v' v /\
          forall T L A, Q v' T L A * dR ==> Q v T L A)) /\
      (word.unsigned br = 0%Z -> (Q v t l a' * R) m))
    (Hpost : forall t m l a, (Q v0 t l a * R0) m -> post t m l a)
    : cmd call (cmd.while e c) t m l a post.
  Proof.
    eexists measure, lt, (fun v t m l a => exists R, (P v t l a * R) m /\
                          forall T L A, Q v T L A * R ==> Q v0 T L A * R0).
    split; [assumption|].
    split. { exists v0, R0. split; [assumption|]. intros. reflexivity. }
    intros vi ti mi li ai (Ri&?&Qi).
    destruct (Hbody _ _ _ _ _ _ ltac:(eassumption)) as (br&a'&?&X); exists br; exists a'; split; [assumption|].
    destruct X as (Htrue&Hfalse). split; intros Hbr;
      [pose proof(Htrue Hbr)as Hpc|pose proof(Hfalse Hbr)as Hpc]; clear Hbr Htrue Hfalse.
    { eapply Proper_cmd; [assumption..| | |eapply Hpc].
      { eapply Proper_call; eauto(*firstorder idtac is very slow here*). }
      intros tj mj lj aj (vj&dR&dP&?&dQ).
      exists vj; split; [|assumption].
      exists (Ri * dR); split; [assumption|].
      intros. rewrite (sep_comm _ dR), <-(sep_assoc _ dR), dQ; trivial. }
    { eapply Hpost, Qi, Hpc. }
  Qed.
End Loops.

Ltac loop_simpl :=
  cbn [reconstruct map.putmany_of_list HList.tuple.to_list
       HList.hlist.foralls HList.tuple.foralls
       HList.hlist.existss HList.tuple.existss
       HList.hlist.apply HList.tuple.apply HList.hlist
       List.repeat Datatypes.length
       HList.polymorphic_list.repeat HList.polymorphic_list.length
       PrimitivePair.pair._1 PrimitivePair.pair._2] in *.
