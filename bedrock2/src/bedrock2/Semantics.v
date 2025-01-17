Require Import coqutil.sanity coqutil.Byte.
Require Import coqutil.Tactics.fwd.
Require Import coqutil.Map.Properties.
Require coqutil.Map.SortedListString.
Require Import bedrock2.Syntax coqutil.Map.Interface coqutil.Map.OfListWord.
Require Import BinIntDef coqutil.Word.Interface coqutil.Word.Bitwidth.
Require Export bedrock2.Memory.
Require Import Coq.Lists.List.

(* BW is not needed on the rhs, but helps infer width *)
Definition LogItem{width: Z}{BW: Bitwidth width}{word: word.word width}{mem: map.map word byte} :=
  ((mem * String.string * list word) * (mem * list word))%type.

Definition trace{width: Z}{BW: Bitwidth width}{word: word.word width}{mem: map.map word byte} :=
  list LogItem.

Definition ExtSpec{width: Z}{BW: Bitwidth width}{word: word.word width}{mem: map.map word byte} :=
  (* Given a trace of what happened so far,
     the given-away memory, an action label and a list of function call arguments, *)
  trace -> mem -> String.string -> list word ->
  (* and a postcondition on the received memory and function call results, *)
  (mem -> list word -> Prop) ->
  (* tells if this postcondition will hold *)
  Prop.

Existing Class ExtSpec.

Module ext_spec.
  Class ok{width: Z}{BW: Bitwidth width}{word: word.word width}{mem: map.map word byte}
          {ext_spec: ExtSpec}: Prop :=
  {
    (* Given a trace of previous interactions, the action name and arguments
       uniquely determine what chunk of memory the ext_spec will chop off from
       the whole memory m *)
    mGive_unique: forall t m mGive1 mKeep1 mGive2 mKeep2 a args post1 post2,
      map.split m mKeep1 mGive1 ->
      map.split m mKeep2 mGive2 ->
      ext_spec t mGive1 a args post1 ->
      ext_spec t mGive2 a args post2 ->
      mGive1 = mGive2;

    #[global] weaken :: forall t mGive act args,
        Morphisms.Proper
          (Morphisms.respectful
             (Morphisms.pointwise_relation Interface.map.rep
               (Morphisms.pointwise_relation (list word) Basics.impl)) Basics.impl)
          (ext_spec t mGive act args);

    intersect: forall t mGive a args
                      (post1 post2: mem -> list word -> Prop),
        ext_spec t mGive a args post1 ->
        ext_spec t mGive a args post2 ->
        ext_spec t mGive a args (fun mReceive resvals =>
                                   post1 mReceive resvals /\ post2 mReceive resvals);
  }.
End ext_spec.
Arguments ext_spec.ok {_ _ _ _} _.

Section binops.
  Context {width : Z} {word : Word.Interface.word width}.
  Definition interp_binop (bop : bopname) : word -> word -> word :=
    match bop with
    | bopname.add => word.add
    | bopname.sub => word.sub
    | bopname.mul => word.mul
    | bopname.mulhuu => word.mulhuu
    | bopname.divu => word.divu
    | bopname.remu => word.modu
    | bopname.and => word.and
    | bopname.or => word.or
    | bopname.xor => word.xor
    | bopname.sru => word.sru
    | bopname.slu => word.slu
    | bopname.srs => word.srs
    | bopname.lts => fun a b =>
      if word.lts a b then word.of_Z 1 else word.of_Z 0
    | bopname.ltu => fun a b =>
      if word.ltu a b then word.of_Z 1 else word.of_Z 0
    | bopname.eq => fun a b =>
      if word.eqb a b then word.of_Z 1 else word.of_Z 0
    end.
End binops.

Definition env: map.map String.string Syntax.func := SortedListString.map _.
#[export] Instance env_ok: map.ok env := SortedListString.ok _.

Section semantics.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word byte}.
  Context {locals: map.map String.string word}.
  Context {ext_spec: ExtSpec}.

  (* this is the expr evaluator that is used to verify execution time, the just-correctness-oriented version is below *)
  Section WithMemAndLocals.
    Context (m : mem) (l : locals).

    Local Notation "x <- a ; f" := (match a with Some x => f | None => None end)
      (right associativity, at level 70).

    Fixpoint eval_expr (e : expr) : option word :=
      match e with
      | expr.literal v => Some (word.of_Z v)
      | expr.var x => map.get l x
      | expr.inlinetable aSize t index =>
          index' <- eval_expr index;
          load aSize (map.of_list_word t) index'
      | expr.load aSize a =>
          a' <- eval_expr a;
          load aSize m a'
      | expr.op op e1 e2 =>
          v1 <- eval_expr e1;
          v2 <- eval_expr e2;
          Some (interp_binop op v1 v2)
      | expr.ite c e1 e2 =>
          vc <- eval_expr c;
          eval_expr (if word.eqb vc (word.of_Z 0) then e2 else e1)
      end.

    Fixpoint eval_call_args (arges : list expr) :=
      match arges with
      | e :: tl =>
        v <- eval_expr e;
        args <- eval_call_args tl;
        Some (v :: args)
      | _ => Some nil
    end.

  End WithMemAndLocals.
End semantics.

Module exec. Section WithParams.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word byte}.
  Context {locals: map.map String.string word}.
  Context {ext_spec: ExtSpec}.
  Section WithEnv.
  Context (e: env).

  Implicit Types post : trace -> mem -> locals -> Prop. (* COQBUG: unification finds Type instead of Prop and fails to downgrade *)
  Inductive exec: cmd -> trace -> mem -> locals ->
                  (trace -> mem -> locals -> Prop) -> Prop :=
  | skip: forall t m l post,
      post t m l ->
      exec cmd.skip t m l post
  | set: forall x e t m l post v,
      eval_expr m l e = Some v ->
      post t m (map.put l x v) ->
      exec (cmd.set x e) t m l post
  | unset: forall x t m l post,
      post t m (map.remove l x) ->
      exec (cmd.unset x) t m l post
  | store: forall sz ea ev t m l post a v m',
      eval_expr m l ea = Some a ->
      eval_expr m l ev = Some v ->
      store sz m a v = Some m' ->
      post t m' l ->
      exec (cmd.store sz ea ev) t m l post
  | stackalloc: forall x n body t mSmall l post,
      Z.modulo n (bytes_per_word width) = 0 ->
      (forall a mStack mCombined,
        anybytes a n mStack ->
        map.split mCombined mSmall mStack ->
        exec body t mCombined (map.put l x a)
          (fun t' mCombined' l' =>
            exists mSmall' mStack',
              anybytes a n mStack' /\
              map.split mCombined' mSmall' mStack' /\
              post t' mSmall' l')) ->
      exec (cmd.stackalloc x n body) t mSmall l post
  | if_true: forall t m l e c1 c2 post v,
      eval_expr m l e = Some v ->
      word.unsigned v <> 0 ->
      exec c1 t m l post ->
      exec (cmd.cond e c1 c2) t m l post
  | if_false: forall e c1 c2 t m l post v,
      eval_expr m l e = Some v ->
      word.unsigned v = 0 ->
      exec c2 t m l post ->
      exec (cmd.cond e c1 c2) t m l post
  | seq: forall c1 c2 t m l post mid,
      exec c1 t m l mid ->
      (forall t' m' l', mid t' m' l' -> exec c2 t' m' l' post) ->
      exec (cmd.seq c1 c2) t m l post
  | while_false: forall e c t m l post v,
      eval_expr m l e = Some v ->
      word.unsigned v = 0 ->
      post t m l ->
      exec (cmd.while e c) t m l post
  | while_true: forall e c t m l post v mid,
      eval_expr m l e = Some v ->
      word.unsigned v <> 0 ->
      exec c t m l mid ->
      (forall t' m' l', mid t' m' l' -> exec (cmd.while e c) t' m' l' post) ->
      exec (cmd.while e c) t m l post
  | call: forall binds fname arges t m l post params rets fbody args lf mid,
      map.get e fname = Some (params, rets, fbody) ->
      eval_call_args m l arges = Some args ->
      map.of_list_zip params args = Some lf ->
      exec fbody t m lf mid ->
      (forall t' m' st1, mid t' m' st1 ->
          exists retvs, map.getmany_of_list st1 rets = Some retvs /\
          exists l', map.putmany_of_list_zip binds retvs l = Some l' /\
          post t' m' l') ->
      exec (cmd.call binds fname arges) t m l post
  | interact: forall binds action arges args t m l post mKeep mGive mid,
      map.split m mKeep mGive ->
      eval_call_args m l arges = Some args ->
      ext_spec t mGive action args mid ->
      (forall mReceive resvals, mid mReceive resvals ->
          exists l', map.putmany_of_list_zip binds resvals l = Some l' /\
          forall m', map.split m' mKeep mReceive ->
          post (cons ((mGive, action, args), (mReceive, resvals)) t) m' l') ->
      exec (cmd.interact binds action arges) t m l post.

  Context {word_ok: word.ok word} {mem_ok: map.ok mem} {ext_spec_ok: ext_spec.ok ext_spec}.

  Lemma interact_cps: forall binds action arges args t m l post mKeep mGive,
      map.split m mKeep mGive ->
      eval_call_args m l arges = Some args ->
      ext_spec t mGive action args (fun mReceive resvals =>
          exists l', map.putmany_of_list_zip binds resvals l = Some l' /\
          forall m', map.split m' mKeep mReceive ->
          post (cons ((mGive, action, args), (mReceive, resvals)) t) m' l') ->
      exec (cmd.interact binds action arges) t m l post.
  Proof. intros. eauto using interact. Qed.

  Lemma seq_cps: forall c1 c2 t m l post,
      exec c1 t m l (fun t' m' l' => exec c2 t' m' l' post) ->
      exec (cmd.seq c1 c2) t m l post.
  Proof. intros. eauto using seq. Qed.

  Lemma weaken: forall t l m s post1,
      exec s t m l post1 ->
      forall post2,
        (forall t' m' l', post1 t' m' l' -> post2 t' m' l') ->
        exec s t m l post2.
  Proof.
    induction 1; intros; try solve [econstructor; eauto].
    - eapply stackalloc. 1: assumption.
      intros.
      eapply H1; eauto.
      intros. fwd. eauto 10.
    - eapply call.
      4: eapply IHexec.
      all: eauto.
      intros.
      edestruct H3 as (? & ? & ? & ? & ?); [eassumption|].
      eauto 10.
    - eapply interact; try eassumption.
      intros.
      edestruct H2 as (? & ? & ?); [eassumption|].
      eauto 10.
  Qed.

  Lemma intersect: forall t l m s post1,
      exec s t m l post1 ->
      forall post2,
        exec s t m l post2 ->
        exec s t m l (fun t' m' l' => post1 t' m' l' /\ post2 t' m' l').
  Proof.
    induction 1;
      intros;
      match goal with
      | H: exec _ _ _ _ _ |- _ => inversion H; subst; clear H
      end;
      try match goal with
      | H1: ?e = Some (?x1, ?y1, ?z1), H2: ?e = Some (?x2, ?y2, ?z2) |- _ =>
        replace x2 with x1 in * by congruence;
          replace y2 with y1 in * by congruence;
          replace z2 with z1 in * by congruence;
          clear x2 y2 z2 H2
      end;
      repeat match goal with
             | H1: ?e = Some ?v1, H2: ?e = Some ?v2 |- _ =>
               replace v2 with v1 in * by congruence; clear H2
             end;
      repeat match goal with
             | H1: ?e = Some ?v1, H2: ?e = Some ?v2 |- _ =>
               replace v2 with v1 in * by congruence; clear H2
             end;
      try solve [econstructor; eauto | exfalso; congruence].

    - econstructor. 1: eassumption.
      intros.
      rename H0 into Ex1, H11 into Ex2.
      eapply weaken. 1: eapply H1. 1,2: eassumption.
      1: eapply Ex2. 1,2: eassumption.
      cbv beta.
      intros. fwd.
      lazymatch goal with
      | A: map.split _ _ _, B: map.split _ _ _ |- _ =>
        specialize @map.split_diff with (4 := A) (5 := B) as P
      end.
      edestruct P; try typeclasses eauto. 2: subst; eauto 10.
      eapply anybytes_unique_domain; eassumption.
    - econstructor.
      + eapply IHexec. exact H5. (* not H *)
      + simpl. intros *. intros [? ?]. eauto.
    - eapply while_true. 1, 2: eassumption.
      + eapply IHexec. exact H9. (* not H1 *)
      + simpl. intros *. intros [? ?]. eauto.
    - eapply call. 1, 2, 3: eassumption.
      + eapply IHexec. exact H15. (* not H2 *)
      + simpl. intros *. intros [? ?].
        edestruct H3 as (? & ? & ? & ? & ?); [eassumption|].
        edestruct H16 as (? & ? & ? & ? & ?); [eassumption|].
        repeat match goal with
               | H1: ?e = Some ?v1, H2: ?e = Some ?v2 |- _ =>
                 replace v2 with v1 in * by congruence; clear H2
               end.
        eauto 10.
    - pose proof ext_spec.mGive_unique as P.
      specialize P with (1 := H) (2 := H7) (3 := H1) (4 := H13).
      subst mGive0.
      destruct (map.split_diff (map.same_domain_refl mGive) H H7) as (? & _).
      subst mKeep0.
      eapply interact. 1,2: eassumption.
      + eapply ext_spec.intersect; [ exact H1 | exact H13 ].
      + simpl. intros *. intros [? ?].
        edestruct H2 as (? & ? & ?); [eassumption|].
        edestruct H14 as (? & ? & ?); [eassumption|].
        repeat match goal with
               | H1: ?e = Some ?v1, H2: ?e = Some ?v2 |- _ =>
                 replace v2 with v1 in * by congruence; clear H2
               end.
        eauto 10.
  Qed.

  Print cmd.
  Fixpoint rm_some_dead (s : cmd) :=
    match s with
    | cmd.stackalloc x n cmd.skip => cmd.skip
    | cmd.stackalloc x n body => cmd.stackalloc x n (rm_some_dead body)
    | cmd.cond c i e => cmd.cond c (rm_some_dead i) (rm_some_dead e)
    | cmd.seq s1 s2 => cmd.seq (rm_some_dead s1) (rm_some_dead s2)
    | cmd.while c body => cmd.while c (rm_some_dead body)
    | _ => s
    end.

  Lemma rm_some_dead_correct s t m l post :
    exec s t m l post -> exec (rm_some_dead s) t m l post.
  Proof.
    intros H. induction H; try solve [econstructor; eauto].
    simpl. destruct body; try solve [econstructor; eauto].
    econstructor.
  Abort.

  Check eval_expr.
  Lemma mextend_expr (m0 : mem) m l ex v :
      map.extends m0 m ->
      eval_expr m l ex = Some v ->
      eval_expr m0 l ex = Some v.
  Proof.
    intros * H H0. revert v H0. induction ex; intros; simpl in *; eauto.
    - destruct (eval_expr m l ex); try discriminate H0. erewrite IHex by reflexivity.
      Print map.extends. cbv [load load_Z]. Search load. (* :( *)
  Admitted.

  Lemma mextend s t m m0 trash l post :
    map.split m0 m trash ->
    exec s t m l post ->
    exec s t m0 l (fun t m0' l => exists m', map.split m0' m' trash /\ post t m' l).
  Proof.
    (*intros Hextends Hexec.
    assert (Hext : map.extends m0 m).
    { intros H w H0. Search map.split. eapply map.get_split_grow_r; eassumption. }*)
    (*assert (Hext' : forall l e v, eval_expr m l e = Some v -> eval_expr m0 l e = Some v).
    { intros. eapply mextend_expr; eassumption. }*)
    intros Hm0 Hexec. revert m0 Hm0. induction Hexec.
    5: { intros m0 Hm0. econstructor; eauto. intros. eapply weaken. 1: eapply H1.
         4: { simpl. intros. fwd. exists (map.putmany mSmall' trash), mStack'.
              split; [assumption|]. split.
              { split.
                2: { intro. intros.
                   (*proof: cant have k in mSmall' since mSmall' disjoint from mStack'.
                    cant have k in trash since k is in mStack' is in m'0, whcih is disjoint from trash*)
                     admit. }
                apply map.map_ext. intros.
                rewrite map.get_putmany_dec.
                destruct (map.get mStack' k) eqn:E.
                - destruct H4p0. subst. destruct H4p1p1. subst.
                  do 2 rewrite map.get_putmany_dec. rewrite E.
                  destruct (map.get trash k) eqn:E'; try reflexivity.
                  exfalso. eapply H5. 2: eassumption. rewrite map.get_putmany_dec.
                  rewrite E. reflexivity.
                - destruct H4p0.  subst. do 2 rewrite map.get_putmany_dec.
                  destruct (map.get trash k); try reflexivity.
                  destruct H4p1p1.  subst. rewrite map.get_putmany_dec. rewrite E.
                  reflexivity. }
              exists mSmall'. split; [|assumption].
              Search (map.split (map.putmany _ _) _ _). apply map.split_disjoint_putmany.
              (*proof: small' is in m'0, which is disjoint from trash*) admit. }
         1: eassumption.
         { instantiate (1 := map.putmany mSmall mStack).
           apply map.split_disjoint_putmany.
           (*proof: mSmall subset of m0, whcih is disj from mStack*)
           admit. }
         destruct H3. subst. destruct Hm0. subst. Check map.putmany_assoc.
         rewrite <- map.putmany_assoc. rewrite (map.putmany_comm trash).
         1: rewrite map.putmany_assoc. 1: apply map.split_disjoint_putmany.
         - Search (map.disjoint (map.putmany _ _)). apply map.disjoint_putmany_l.
           split; [assumption|]. apply map.disjoint_putmany_l in H4. destruct H4.
           apply map.disjoint_comm. assumption.
         - apply map.disjoint_putmany_l in H4. destruct H4. assumption. }
    
           
         1: eassumption.
              apply map.split_putmany.
                  fwd.
                Search map.putmany.
                     
              eexists. eexists. split; eauto. split; eauto.
              
         eapply  H1.
    revert m0. induction Hexec; try solve [econstructor; eauto].
    3: { econstructor; eauto. intros. eapply H1. 
    - econstructor; eauto. admit.
      -    - econstructor; eauto. intros. specialize H1 with (5 := Hext'). oeapply H1. econstructor; 
      
      
    - econstructor; eauto. apply mextend_epxr. Search eval_expr.
     
  End WithEnv.

  Lemma extend_env: forall e1 e2,
      map.extends e2 e1 ->
      forall c t m l post,
      exec e1 c t m l post ->
      exec e2 c t m l post.
  Proof. induction 2; try solve [econstructor; eauto]. Qed.

  End WithParams.
End exec. Notation exec := exec.exec.

Section WithParams.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word byte}.
  Context {locals: map.map String.string word}.
  Context {ext_spec: ExtSpec}.

  Implicit Types (l: locals) (m: mem) (post: trace -> mem -> list word -> Prop).

  Definition call e fname t m args post :=
    exists argnames retnames body,
      map.get e fname = Some (argnames, retnames, body) /\
      exists l, map.of_list_zip argnames args = Some l /\
        exec e body t m l (fun t' m' l' => exists rets,
          map.getmany_of_list l' retnames = Some rets /\ post t' m' rets).

  Lemma weaken_call: forall e fname t m args post1,
      call e fname t m args post1 ->
      forall post2, (forall t' m' rets, post1 t' m' rets -> post2 t' m' rets) ->
      call e fname t m args post2.
  Proof.
    unfold call. intros. fwd.
    do 4 eexists. 1: eassumption.
    do 2 eexists. 1: eassumption.
    eapply exec.weaken. 1: eassumption.
    cbv beta. clear -H0. intros. fwd. eauto.
  Qed.

  Lemma extend_env_call: forall e1 e2,
      map.extends e2 e1 ->
      forall f t m rets post,
      call e1 f t m rets post ->
      call e2 f t m rets post.
  Proof.
    unfold call. intros. fwd. repeat eexists.
    - eapply H. eassumption.
    - eassumption.
    - eapply exec.extend_env; eassumption.
  Qed.
End WithParams.
