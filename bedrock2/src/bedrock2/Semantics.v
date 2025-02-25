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

  Implicit Types post : bool -> trace -> mem -> locals -> Prop. (* COQBUG: unification finds Type instead of Prop and fails to downgrade *)
  Inductive exec: cmd -> bool -> trace -> mem -> locals ->
                  (bool -> trace -> mem -> locals -> Prop) -> Prop :=
  | skip: forall t m l post,
      post true t m l ->
      exec cmd.skip true t m l post
  | set: forall x e t m l post v,
      eval_expr m l e = Some v ->
      post true t m (map.put l x v) ->
      exec (cmd.set x e) true t m l post
  | unset: forall x t m l post,
      post true t m (map.remove l x) ->
      exec (cmd.unset x) true t m l post
  | store: forall sz ea ev t m l post a v m',
      eval_expr m l ea = Some a ->
      eval_expr m l ev = Some v ->
      store sz m a v = Some m' ->
      post true t m' l ->
      exec (cmd.store sz ea ev) true t m l post
  | stackalloc: forall x n body t mSmall l post,
      Z.modulo n (bytes_per_word width) = 0 ->
      (forall a mStack mCombined,
        anybytes a n mStack ->
        map.split mCombined mSmall mStack ->
        exec body true t mCombined (map.put l x a)
          (fun true' t' mCombined' l' =>
            exists mSmall' mStack',
              anybytes a n mStack' /\
              map.split mCombined' mSmall' mStack' /\
              post true' t' mSmall' l')) ->
      exec (cmd.stackalloc x n body) true t mSmall l post
  | if_true: forall t m l e c1 c2 post v,
      eval_expr m l e = Some v ->
      word.unsigned v <> 0 ->
      exec c1 true t m l post ->
      exec (cmd.cond e c1 c2) true t m l post
  | if_false: forall e c1 c2 t m l post v,
      eval_expr m l e = Some v ->
      word.unsigned v = 0 ->
      exec c2 true t m l post ->
      exec (cmd.cond e c1 c2) true t m l post
  | seq: forall c1 c2 t m l post mid,
      exec c1 true t m l mid ->
      (forall true' t' m' l', mid true' t' m' l' -> exec c2 true' t' m' l' post) ->
      exec (cmd.seq c1 c2) true t m l post
  | while_false: forall e c t m l post v,
      eval_expr m l e = Some v ->
      word.unsigned v = 0 ->
      post true t m l ->
      exec (cmd.while e c) true t m l post
  | while_true: forall e c t m l post v mid,
      eval_expr m l e = Some v ->
      word.unsigned v <> 0 ->
      exec c true t m l mid ->
      (forall true' t' m' l', mid true' t' m' l' -> exec (cmd.while e c) true' t' m' l' post) ->
      exec (cmd.while e c) true t m l post
  | call: forall binds fname arges t m l post params rets fbody args lf mid,
      map.get e fname = Some (params, rets, fbody) ->
      eval_call_args m l arges = Some args ->
      map.of_list_zip params args = Some lf ->
      exec fbody true t m lf mid ->
      (forall true' t' m' st1, mid true' t' m' st1 ->
          exists retvs, map.getmany_of_list st1 rets = Some retvs /\
          exists l', map.putmany_of_list_zip binds retvs l = Some l' /\
          post true' t' m' l') ->
      exec (cmd.call binds fname arges) true t m l post
  | interact: forall binds action arges args t m l post mKeep mGive mid,
      map.split m mKeep mGive ->
      eval_call_args m l arges = Some args ->
      ext_spec t mGive action args mid ->
      (forall mReceive resvals, mid mReceive resvals ->
          exists l', map.putmany_of_list_zip binds resvals l = Some l' /\
          forall m', map.split m' mKeep mReceive ->
          post true (cons ((mGive, action, args), (mReceive, resvals)) t) m' l') ->
      exec (cmd.interact binds action arges) true t m l post
  | quit: forall c q t m l post,
      post false t m l ->
      exec c q t m l post.

  Context {word_ok: word.ok word} {mem_ok: map.ok mem} {ext_spec_ok: ext_spec.ok ext_spec}.

  Lemma interact_cps: forall binds action arges args t m l post mKeep mGive,
      map.split m mKeep mGive ->
      eval_call_args m l arges = Some args ->
      ext_spec t mGive action args (fun mReceive resvals =>
          exists l', map.putmany_of_list_zip binds resvals l = Some l' /\
          forall m', map.split m' mKeep mReceive ->
          post true (cons ((mGive, action, args), (mReceive, resvals)) t) m' l') ->
      exec (cmd.interact binds action arges) true t m l post.
  Proof. intros. eauto using interact. Qed.

  Lemma seq_cps: forall c1 c2 t m l post,
      exec c1 true t m l (fun q' t' m' l' => exec c2 q' t' m' l' post) ->
      exec (cmd.seq c1 c2) true t m l post.
  Proof. intros. eauto using seq. Qed.

  Lemma weaken: forall q t l m s post1,
      exec s q t m l post1 ->
      forall post2,
        (forall q' t' m' l', post1 q' t' m' l' -> post2 q' t' m' l') ->
        exec s q t m l post2.
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

  Lemma intersect: forall s q t m l post1,
      (forall t m l, post1 false t m l -> False) ->
      exec s q t m l post1 ->
      forall post2,
        (forall t m l, post2 false t m l -> False) ->
        exec s q t m l post2 ->
        exec s q t m l (fun q' t' m' l' => post1 q' t' m' l' /\ post2 q' t' m' l').
  Proof.
    intros * Hpost1.
    induction 1;
      intros post2 Hpost2 ?;
      match goal with
      | H: exec _ _ _ _ _ _ |- _ => inversion H;
                                  try solve [exfalso; eauto];
                                  subst; clear H
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
  Abort. (*this should be true, but looks like a few minutes of effort*)
    (*   intros. *)
    (*   rename H0 into Ex1, H12 into Ex2. *)
    (*   eapply weaken. 1: eapply H1. 1,2: eassumption. *)
    (*   { intros. fwd. eauto. } *)
    (*   2: eapply Ex2. *)
    (*   { simpl. intros. fwd. eauto. } *)
    (*   1,2: eassumption. *)
    (*   cbv beta. *)
    (*   intros. fwd. *)
    (*   lazymatch goal with *)
    (*   | A: map.split _ _ _, B: map.split _ _ _ |- _ => *)
    (*     specialize @map.split_diff with (4 := A) (5 := B) as P *)
    (*   end. *)
    (*   edestruct P; try typeclasses eauto. 2: subst; eauto 10. *)
    (*   eapply anybytes_unique_domain; eassumption. *)
    (* - econstructor. *)
    (*   + eapply weaken. 1: eapply IHexec. *)
  (*       --  *)
  (*       exact H5. (* not H *) *)
  (*     + simpl. intros *. intros [? ?]. eauto. *)
  (*   - eapply while_true. 1, 2: eassumption. *)
  (*     + eapply IHexec. exact H9. (* not H1 *) *)
  (*     + simpl. intros *. intros [? ?]. eauto. *)
  (*   - eapply call. 1, 2, 3: eassumption. *)
  (*     + eapply IHexec. exact H16. (* not H2 *) *)
  (*     + simpl. intros *. intros [? ?]. *)
  (*       edestruct H3 as (? & ? & ? & ? & ?); [eassumption|]. *)
  (*       edestruct H17 as (? & ? & ? & ? & ?); [eassumption|]. *)
  (*       repeat match goal with *)
  (*              | H1: ?e = Some ?v1, H2: ?e = Some ?v2 |- _ => *)
  (*                replace v2 with v1 in * by congruence; clear H2 *)
  (*              end. *)
  (*       eauto 10. *)
  (*   - pose proof ext_spec.mGive_unique as P. *)
  (*     specialize P with (1 := H) (2 := H7) (3 := H1) (4 := H14). *)
  (*     subst mGive0. *)
  (*     destruct (map.split_diff (map.same_domain_refl mGive) H H7) as (? & _). *)
  (*     subst mKeep0. *)
  (*     eapply interact. 1,2: eassumption. *)
  (*     + eapply ext_spec.intersect; [ exact H1 | exact H14 ]. *)
  (*     + simpl. intros *. intros [? ?]. *)
  (*       edestruct H2 as (? & ? & ?); [eassumption|]. *)
  (*       edestruct H15 as (? & ? & ?); [eassumption|]. *)
  (*       repeat match goal with *)
  (*              | H1: ?e = Some ?v1, H2: ?e = Some ?v2 |- _ => *)
  (*                replace v2 with v1 in * by congruence; clear H2 *)
  (*              end. *)
  (*       eauto 10. *)
  (* Qed. *)

  End WithEnv.

  Lemma extend_env: forall e1 e2,
      map.extends e2 e1 ->
      forall c q t m l post,
      exec e1 c q t m l post ->
      exec e2 c q t m l post.
  Proof. induction 2; try solve [econstructor; eauto]. Qed.

  End WithParams.
End exec. Notation exec := exec.exec.

Section WithParams.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word byte}.
  Context {locals: map.map String.string word}.
  Context {ext_spec: ExtSpec}.

  Implicit Types (l: locals) (m: mem) (post: bool -> trace -> mem -> list word -> Prop).

  Definition call e fname q t m args post :=
    exists argnames retnames body,
      map.get e fname = Some (argnames, retnames, body) /\
      exists l, map.of_list_zip argnames args = Some l /\
        exec e body q t m l (fun q' t' m' l' => exists rets,
          map.getmany_of_list l' retnames = Some rets /\ post q' t' m' rets).

  Lemma weaken_call: forall e fname q t m args post1,
      call e fname q t m args post1 ->
      forall post2, (forall q' t' m' rets, post1 q' t' m' rets -> post2 q' t' m' rets) ->
      call e fname q t m args post2.
  Proof.
    unfold call. intros. fwd.
    do 4 eexists. 1: eassumption.
    do 2 eexists. 1: eassumption.
    eapply exec.weaken. 1: eassumption.
    cbv beta. clear -H0. intros. fwd. eauto.
  Qed.

  Lemma extend_env_call: forall e1 e2,
      map.extends e2 e1 ->
      forall f q t m rets post,
      call e1 f q t m rets post ->
      call e2 f q t m rets post.
  Proof.
    unfold call. intros. fwd. repeat eexists.
    - eapply H. eassumption.
    - eassumption.
    - eapply exec.extend_env; eassumption.
  Qed.
End WithParams.

Require Import coqutil.Word.SimplWordExpr.
From Coq Require Import ZArith.
From Coq Require Import Lia.

Section WithParams.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word byte}.
  Context {locals: map.map String.string word}.
  Context {word_ok : word.ok word} {mem_ok: map.ok mem}.

  Instance ext_spec : ExtSpec := fun t m action args post =>
                                   post map.empty nil.

  Definition example := cmd.while (expr.literal 1) (cmd.interact nil String.EmptyString nil).

  Lemma one_not_zero : word.unsigned (word := word) (word.of_Z 1) <> 0.
  Proof.
    rewrite word.unsigned_of_Z. cbv [word.wrap]. 
    destruct word_ok. clear - width_pos.
    assert (2 ^ 1 <= 2 ^ width).
    { Search (_ ^ _ <= _ ^ _).  apply Z.pow_le_mono_r; lia. }
    replace (2 ^ 1) with 2 in H by reflexivity.
    remember (2 ^ width) as blah. clear Heqblah.
    Fail Z.div_mod_to_equations; lia. (*?*)
    rewrite Z.mod_small by lia. lia.
  Qed.
  
  Lemma goes_forever' e n t m l :
      exec e example true t m l
        (fun q' t' m' l' => q' = false /\ length t' = length t + n)%nat.
  Proof.
    revert t m l. induction n; intros t m l.
    - apply exec.quit. auto.
    - eapply exec.while_true with (mid := fun q0 t0 m0 l0 => q0 = true /\ t0 = _ :: t /\ m0 = m /\ l0 = l).
      + reflexivity.
      + apply one_not_zero.
      + eapply exec.interact_cps.
        -- Search (map.split _ _ map.empty). apply map.split_empty_r. reflexivity.
        -- reflexivity.
        -- cbv [ext_spec]. eexists. intuition eauto.
           apply map.split_empty_r. assumption.
      + intros. fwd. eapply exec.weaken. 1: apply IHn. simpl. intros. fwd.
        intuition auto. lia.
  Qed.

  Lemma goes_forever e m l :
    forall n,
    exec e example true nil m l
      (fun q' t' m' l' => q' = false /\ length t' = n).
  Proof.
    intros. eapply exec.weaken. 1: apply goes_forever'. simpl. intros. fwd. eauto.
  Qed.
End WithParams.
