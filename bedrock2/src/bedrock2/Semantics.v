Require Import coqutil.sanity coqutil.Byte.
Require Import coqutil.Tactics.fwd coqutil.Tactics.Tactics.
Require Import coqutil.Map.Properties.
Require coqutil.Map.SortedListString.
Require Import bedrock2.Syntax coqutil.Map.Interface coqutil.Map.OfListWord.
Require Import BinIntDef coqutil.Word.Interface coqutil.Word.Bitwidth.
Require Export bedrock2.Memory.
Require Import Coq.Lists.List.
Import ListNotations.

Require Import Coq.ZArith.BinInt.
Require Import Coq.micromega.Lia.
Require Coq.Arith.PeanoNat.
Require Import bedrock2.Array.

Open Scope Z_scope.


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
      (* | expr.inlinetable aSize t index => *)
      (*     index' <- eval_expr index; *)
      (*     load aSize (map.of_list_word t) index' *)
      (* | expr.load aSize a => *)
      (*     a' <- eval_expr a; *)
      (*     load aSize m a' *)
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

  Implicit Types post : trace -> list mem -> locals -> Prop. (* COQBUG: unification finds Type instead of Prop and fails to downgrade *)
  Inductive exec: cmd -> trace -> list mem -> locals ->
                  (trace -> list mem -> locals -> Prop) -> Prop :=
  | skip: forall t m l post,
      post t m l ->
      exec cmd.skip t m l post
  | set: forall x e t m l post v,
      eval_expr l e = Some v ->
      post t m (map.put l x v) ->
      exec (cmd.set x e) t m l post
  | unset: forall x t m l post,
      post t m (map.remove l x) ->
      exec (cmd.unset x) t m l post
  | load: forall x sz e t m mi l post a v,
      eval_expr l e = Some a ->
      In mi m ->
      load sz mi a = Some v ->
      post t m (map.put l x v) ->
      exec (cmd.load x sz e) t m l post
  | store: forall sz ea ev t m l post m1 m2 mi a v mi',
      eval_expr l ea = Some a ->
      eval_expr l ev = Some v ->
      m = m1 ++ [mi] ++ m2 ->
      store sz mi a v = Some mi' ->
      post t (m1 ++ [mi'] ++ m2) l ->
      exec (cmd.store sz ea ev) t m l post
  | stackalloc: forall x n body t mSmall l post,
      Z.modulo n (bytes_per_word width) = 0 ->
      (forall a mStack,
        anybytes a n mStack ->
        exec body t (mStack :: mSmall) (map.put l x a)
          (fun t' mCombined' l' =>
             exists mSmall' mStack',
               mCombined' = mStack' :: mSmall' /\
                 anybytes a n mStack' /\
                 post t' mSmall' l')) ->
      exec (cmd.stackalloc x n body) t mSmall l post
  | if_true: forall t m l e c1 c2 post v,
      eval_expr l e = Some v ->
      word.unsigned v <> 0 ->
      exec c1 t m l post ->
      exec (cmd.cond e c1 c2) t m l post
  | if_false: forall e c1 c2 t m l post v,
      eval_expr l e = Some v ->
      word.unsigned v = 0 ->
      exec c2 t m l post ->
      exec (cmd.cond e c1 c2) t m l post
  | seq: forall c1 c2 t m l post mid,
      exec c1 t m l mid ->
      (forall t' m' l', mid t' m' l' -> exec c2 t' m' l' post) ->
      exec (cmd.seq c1 c2) t m l post
  | while_false: forall e c t m l post v,
      eval_expr l e = Some v ->
      word.unsigned v = 0 ->
      post t m l ->
      exec (cmd.while e c) t m l post
  | while_true: forall e c t m l post v mid,
      eval_expr l e = Some v ->
      word.unsigned v <> 0 ->
      exec c t m l mid ->
      (forall t' m' l', mid t' m' l' -> exec (cmd.while e c) t' m' l' post) ->
      exec (cmd.while e c) t m l post
  | call: forall binds fname arges t m l post params rets fbody args lf mid,
      map.get e fname = Some (params, rets, fbody) ->
      eval_call_args l arges = Some args ->
      map.of_list_zip params args = Some lf ->
      exec fbody t m lf mid ->
      (forall t' m' st1, mid t' m' st1 ->
          exists retvs, map.getmany_of_list st1 rets = Some retvs /\
          exists l', map.putmany_of_list_zip binds retvs l = Some l' /\
          post t' m' l') ->
      exec (cmd.call binds fname arges) t m l post
  .

  Context {word_ok: word.ok word} {mem_ok: map.ok mem} {ext_spec_ok: ext_spec.ok ext_spec}.

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
  Qed.

  End WithEnv.

  Lemma extend_env: forall e1 e2,
      map.extends e2 e1 ->
      forall c t m l post,
      exec e1 c t m l post ->
      exec e2 c t m l post.
  Proof. induction 2; try solve [econstructor; eauto]. Qed.

  End WithParams.
End exec. Notation exec := exec.exec.

Module oldexec. Section WithParams.
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
      eval_expr l e = Some v ->
      post t m (map.put l x v) ->
      exec (cmd.set x e) t m l post
  | unset: forall x t m l post,
      post t m (map.remove l x) ->
      exec (cmd.unset x) t m l post
  | load: forall x sz e t m l post a v,
      eval_expr l e = Some a ->
      load sz m a = Some v ->
      post t m (map.put l x v) ->
      exec (cmd.load x sz e) t m l post
  | store: forall sz ea ev t m l post a v m',
      eval_expr l ea = Some a ->
      eval_expr l ev = Some v ->
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
      eval_expr l e = Some v ->
      word.unsigned v <> 0 ->
      exec c1 t m l post ->
      exec (cmd.cond e c1 c2) t m l post
  | if_false: forall e c1 c2 t m l post v,
      eval_expr l e = Some v ->
      word.unsigned v = 0 ->
      exec c2 t m l post ->
      exec (cmd.cond e c1 c2) t m l post
  | seq: forall c1 c2 t m l post mid,
      exec c1 t m l mid ->
      (forall t' m' l', mid t' m' l' -> exec c2 t' m' l' post) ->
      exec (cmd.seq c1 c2) t m l post
  | while_false: forall e c t m l post v,
      eval_expr l e = Some v ->
      word.unsigned v = 0 ->
      post t m l ->
      exec (cmd.while e c) t m l post
  | while_true: forall e c t m l post v mid,
      eval_expr l e = Some v ->
      word.unsigned v <> 0 ->
      exec c t m l mid ->
      (forall t' m' l', mid t' m' l' -> exec (cmd.while e c) t' m' l' post) ->
      exec (cmd.while e c) t m l post
  | call: forall binds fname arges t m l post params rets fbody args lf mid,
      map.get e fname = Some (params, rets, fbody) ->
      eval_call_args l arges = Some args ->
      map.of_list_zip params args = Some lf ->
      exec fbody t m lf mid ->
      (forall t' m' st1, mid t' m' st1 ->
          exists retvs, map.getmany_of_list st1 rets = Some retvs /\
          exists l', map.putmany_of_list_zip binds retvs l = Some l' /\
          post t' m' l') ->
      exec (cmd.call binds fname arges) t m l post
  .

  Context {word_ok: word.ok word} {mem_ok: map.ok mem} {ext_spec_ok: ext_spec.ok ext_spec}.

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
  Qed.

  End WithEnv.

  Lemma extend_env: forall e1 e2,
      map.extends e2 e1 ->
      forall c t m l post,
      exec e1 c t m l post ->
      exec e2 c t m l post.
  Proof. induction 2; try solve [econstructor; eauto]. Qed.

  End WithParams.
End oldexec. Notation oldexec := oldexec.exec.

Section WithParams.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word byte}.
  Context {locals: map.map String.string word}.
  Context {word_ok: word.ok word} {mem_ok: map.ok mem}.
  Context {ext_spec: ExtSpec}.

  Implicit Types (l: locals) (m: list mem) (post: trace -> list mem -> locals -> Prop).

  Inductive all_disj : list mem -> Prop :=
  | nil_disj : all_disj []
  | cons_disj m mi : all_disj m ->
                     (forall mj, In mj m -> map.disjoint mi mj) ->
                     all_disj (mi :: m).

  Lemma all_disj_alt mi m :
    all_disj (mi :: m) ->
    map.disjoint mi (fold_right map.putmany map.empty m).
  Proof.
    induction m.
    - intros _. simpl. apply map.disjoint_empty_r.
    - intros H. simpl.
      apply map.disjoint_putmany_r. 
      inversion H. subst. clear H.
      split.
      + apply H3. left. reflexivity.
      + apply IHm. constructor.
        -- inversion H2. subst. assumption.
        -- intros. apply H3. right. assumption.
  Qed.

  Lemma all_disj_alt_conv mi m :
    map.disjoint mi (fold_right map.putmany map.empty m) ->
    (forall mj : mem, In mj m -> map.disjoint mi mj).
  Proof.
    intros H. induction m; intros mj Hin.
    - destruct Hin.
    - simpl in H. apply map.disjoint_putmany_r in H. destruct H as [H1 H2].
      destruct Hin as [Hin|Hin].
      + subst. assumption.
      + apply IHm; assumption.
  Qed.

  Lemma all_disj_putmany_commute m :
    all_disj m ->
    fold_right map.putmany map.empty m = fold_right (fun x y => map.putmany y x) map.empty m.
  Proof.
    induction m; intros Hdisj; [reflexivity|]. inversion Hdisj. subst.
    specialize (IHm ltac:(assumption)). simpl. rewrite <- IHm. apply map.putmany_comm.
    apply all_disj_alt. assumption.
  Qed.

  Lemma all_disj_get m mi a v :
    all_disj m ->
    In mi m ->
    map.get mi a = Some v ->
    map.get (fold_right map.putmany map.empty m) a = Some v.
  Proof.
    induction m.
    - intros _ contra. destruct contra.
    - intros Hdisj Hin Hget. inversion Hdisj. subst. specialize (IHm H1).
      rewrite all_disj_putmany_commute by assumption. simpl.
      rewrite <- all_disj_putmany_commute by assumption.
      inversion Hin; subst.
      + apply map.get_putmany_right. assumption.
      + rewrite map.get_putmany_left.
        -- apply IHm; assumption.
        -- specialize (H2 _ H).
           clear -H2 Hget. cbv [map.disjoint] in H2. specialize (H2 a).
           destruct (map.get a0 a); [|reflexivity]. exfalso. eapply H2; eauto.
  Qed.

  Lemma put_putmany_assoc (mi mj : mem) a v :
    map.get mj a = None ->
    map.put (map.putmany mi mj) a v = map.putmany (map.put mi a v) mj.
  Proof.
    rewrite map.put_putmany_commute.
    replace (map.put mi a v) with (map.putmany mi (map.put map.empty a v)).
    2: { rewrite <- map.put_putmany_commute.
         rewrite map.putmany_empty_r.
         reflexivity. }
    rewrite <- map.putmany_assoc.
    intros H. f_equal.
    rewrite map.putmany_comm.
    - rewrite <- map.put_putmany_commute. rewrite map.putmany_empty_r. reflexivity.
    - apply map.disjoint_put_l; [assumption|]. apply map.disjoint_empty_l.
  Qed.

  Lemma all_disj_put m m1 mi m2 a v0 v :
    all_disj m ->
    m = m1 ++ [mi] ++ m2 ->
    map.get mi a = Some v0 ->
    map.put (fold_right map.putmany map.empty m) a v = fold_right map.putmany map.empty (m1 ++ [map.put mi a v] ++ m2).
  Proof.
    intros H1 H2. subst. revert H1. induction m1; simpl; intros Hdisj Hget.
    - inversion Hdisj. subst. apply put_putmany_assoc.
      destruct (map.get (fold_right _ _ _) _) eqn:E; [|reflexivity].
      exfalso. eapply all_disj_alt; eassumption.
    - rewrite map.put_putmany_commute. f_equal. apply IHm1; [|assumption].
      inversion Hdisj. subst. assumption.
  Qed.                                                            
    
  Lemma all_disj_getmany_of_tuple sz m mi keys v :
    all_disj m ->
    In mi m ->
    @map.getmany_of_tuple _ _ _ mi sz keys = Some v ->
    @map.getmany_of_tuple _ _ _ (fold_right map.putmany map.empty m) sz keys  = Some v.
  Proof.
    intros Hdisj HIn. pose proof all_disj_get as Hget.
    specialize Hget with (1 := Hdisj) (2 := HIn).
    induction sz.
    - destruct keys. cbv [map.getmany_of_tuple]. simpl. auto.
    - destruct keys. cbn [map.getmany_of_tuple]. cbv [map.getmany_of_tuple]. simpl.
      destruct_one_match; [|congruence]. apply Hget in E. rewrite E.
      destruct_one_match; [|congruence]. intros H. inversion H. clear H. subst.
      apply IHsz in E0. cbv [map.getmany_of_tuple] in E0. rewrite E0. reflexivity.
  Qed.

  Lemma all_disj_sub_domain (mi mj : mem) m1 m2 :
    map.sub_domain mj mi ->
    all_disj (m1 ++ [mi] ++ m2) ->
    all_disj (m1 ++ [mj] ++ m2).
  Proof.
    intros H1 H2. induction m1; simpl in *.
    - inversion H2. subst. constructor; [assumption|]. intros.
      eapply map.sub_domain_disjoint; eauto.
    - inversion H2. subst. constructor; [solve[auto]|]. intros.
      apply in_app_iff in H. destruct H as [H|H].
      + apply H4. apply in_app_iff. left. assumption.
      + destruct H as [H|H].
        -- subst. apply map.disjoint_comm.
           eapply map.sub_domain_disjoint; [|eassumption]. clear -H2 word_ok mem_ok.
           inversion H2. subst. apply map.disjoint_comm.
           apply H3. apply in_app_iff. right. left. reflexivity.
        -- apply H4. apply in_app_iff. right. right. assumption.
  Qed.
 
  Lemma all_disj_putmany_of_tuple sz m mi m1 m2 keys v v0 :
    all_disj m ->
    m = m1 ++ [mi] ++ m2 ->
    @map.getmany_of_tuple _ _ _ mi sz keys = Some v0 ->
    @map.putmany_of_tuple _ _ _ _ keys v (fold_right map.putmany map.empty m) = fold_right map.putmany map.empty (m1 ++ [@map.putmany_of_tuple _ _ _ _ keys v mi] ++ m2).
  Proof.
    intros Hdisj Hmi. pose proof all_disj_put as Hput. subst.
    induction sz.
    - destruct keys. cbv [map.getmany_of_tuple]. simpl. auto.
    - destruct keys. cbv [map.getmany_of_tuple]. simpl.
      destruct_one_match; [|congruence]. destruct_one_match; [|congruence].
      intros H. inversion H. clear H. subst. simpl in Hput.
      pose proof E0 as E0'.
      eapply map.putmany_of_tuple_preserves_domain in E0.
      destruct E0 as [E0 E1]. apply E0 in E. fwd.
      erewrite <- Hput.
      3: reflexivity.
      2: { eapply all_disj_sub_domain.  2: eassumption. apply E1. }
      2: eassumption.
      specialize IHsz with (1 := E0'). rewrite IHsz. reflexivity.
  Qed.

  Lemma all_disj_store m m1 m2 sz mi mi' a v :
    all_disj m ->
    m = m1 ++ [mi] ++ m2 ->
    store sz mi a v = Some mi' ->
    store sz (fold_right map.putmany map.empty m) a v = Some (fold_right map.putmany map.empty (m1 ++ [mi'] ++ m2)).
  Proof.
    intros Hdisj Hmi Hst. cbv [store store_Z store_bytes load_bytes] in *.
    pose proof all_disj_getmany_of_tuple as Hget.
    assert (Hin : In mi m).
    { subst. clear. apply in_app_iff. right. apply in_app_iff. left. repeat constructor. }
    specialize Hget with (1 := Hdisj) (2 := Hin).
    destruct_one_match_hyp; [|congruence]. inversion Hst. clear Hst. subst.
    pose proof E as E'. apply Hget in E'. rewrite E'. clear E'. f_equal.
    eapply all_disj_putmany_of_tuple; eauto.
  Qed.
  
  Lemma all_disj_load m sz mi a v :
    all_disj m ->
    In mi m ->
    load sz mi a = Some v ->
    load sz (fold_right map.putmany map.empty m) a = Some v.
  Proof.
    intros Hdisj Hin Hload. cbv [load load_Z load_bytes] in *.
    pose proof all_disj_getmany_of_tuple as Hget.
    specialize Hget with (1 := Hdisj) (2 := Hin).
    destruct_one_match_hyp; [|congruence]. inversion Hload. subst. clear Hload.
    destruct_one_match_hyp; [|congruence]. inversion E. subst. clear E.
    apply Hget in E0. rewrite E0. reflexivity.
  Qed.

  Inductive same_domain : list mem -> list mem -> Prop :=
  | nil_same : same_domain [] []
  | cons_same mi mi' m m' : map.same_domain mi mi' ->
                            same_domain m m' ->
                            same_domain (mi :: m) (mi' :: m').

  Lemma same_domain_refl m : same_domain m m.
  Proof.
    induction m.
    - constructor.
    - constructor.
      + apply map.same_domain_refl.
      + assumption.
  Qed.

  Lemma same_domain_trans m1 m2 m3 :
    same_domain m1 m2 ->
    same_domain m2 m3 ->
    same_domain m1 m3.
  Proof.
    intros H1 H2. revert m3 H2. induction H1; intros m3 H2.
    - inversion H2. constructor.
    - inversion H2. subst. constructor.
      + eapply map.same_domain_trans; eassumption.
      + eapply IHsame_domain; eassumption.
  Qed.

  Lemma same_domain_app_iff m1 m1' m2 m2' :
    length m1 = length m1' ->
    same_domain (m1 ++ m2) (m1' ++ m2') <-> same_domain m1 m1' /\ same_domain m2 m2'.
  Proof.
    revert m1'. induction m1.
    - intros. destruct m1'; [|discriminate H]. simpl. split; intros.
      + split; [constructor|assumption].
      + fwd. assumption.
    - intros. destruct m1'; [discriminate H|]. injection H as H. apply IHm1 in H.
      clear IHm1. simpl. split; intros.
      + inversion H0. subst. clear H0. rewrite H in H6. fwd. split; [|assumption].
        constructor; assumption.
      + fwd. inversion H0p0. subst. clear H0p0. constructor; [assumption|].
        apply H. clear H. auto.
  Qed.

  Lemma putmany_sub_domain (mi mi' mj mj' : mem) :
    map.sub_domain mi mi' ->
    map.sub_domain mj mj' ->
    map.sub_domain (map.putmany mi mj) (map.putmany mi' mj').
  Proof.
    intros H1 H2. pose proof map.putmany_spec mi mj. pose proof map.putmany_spec mi' mj'.
    intro. intros. specialize (H k). specialize (H0 k).
    destruct H0 as [H0|H0].
    - fwd. eexists. eassumption.
    - destruct H as [H|H].
      + fwd. apply H2 in Hp0. fwd. congruence.
      + fwd. rewrite H0p1. rewrite Hp1 in H3. apply H1 in H3. assumption.
  Qed.

  Lemma putmany_same_domain (mi mi' mj mj' : mem) :
    map.same_domain mi mi' ->
    map.same_domain mj mj' ->
    map.same_domain (map.putmany mi mj) (map.putmany mi' mj').
  Proof.
    intros H1 H2. destruct H1, H2. split; apply putmany_sub_domain; auto.
  Qed.

  Lemma same_domain_flattened m1 m2 :
    same_domain m1 m2 ->
    map.same_domain (fold_right map.putmany map.empty m1) (fold_right map.putmany map.empty m2).
  Proof.
    intros H. induction H.
    - simpl. apply map.same_domain_refl.
    - simpl. apply putmany_same_domain; assumption.
  Qed.

  Lemma same_domain_disj' mi m m' :
    (forall mj, In mj m -> map.disjoint mi mj) ->
    same_domain m m' ->
    (forall mj, In mj m' -> map.disjoint mi mj).
  Proof.
    intros H1 H2. induction H2; [assumption|].
    intros. destruct H0 as [H0|H0].
    - subst. apply map.disjoint_comm. eapply map.sub_domain_disjoint.
      2: apply H. apply map.disjoint_comm. apply H1. left. reflexivity.
    - apply IHsame_domain. 2: assumption. intros. apply H1. right. assumption.
  Qed.

  Lemma same_domain_disj m m' :
    all_disj m ->
    same_domain m m' ->
    all_disj m'.
  Proof.
    intros H1 H2. induction H2; [constructor|].
    inversion H1. subst. clear H1.
    constructor; [solve[auto]|].
    intros. eapply same_domain_disj'; eauto. intros.
    eapply map.sub_domain_disjoint; [|apply H]. apply H5. assumption.
  Qed.
  
  Lemma exec_implies_oldexec' e s t m l post :
    all_disj m ->
    exec e s t m l post ->
    oldexec e s t (fold_right map.putmany map.empty m) l
      (fun t mflat' l =>
         exists m',
           mflat' = fold_right map.putmany map.empty m' /\
             same_domain m m' /\
             post t m' l).
  Proof.
    intros H0 H. revert H0. induction H; intros Hdisj; try solve [econstructor; eauto using same_domain_refl].
    - econstructor; eauto using all_disj_load, same_domain_refl.
    - econstructor; eauto using all_disj_store. eexists. intuition eauto. subst.
      apply same_domain_app_iff; [reflexivity|]. split; [apply same_domain_refl|].
      constructor; [|apply same_domain_refl]. eapply store_preserves_domain.
      eassumption.      
    - econstructor; eauto. intros. destruct H3 as [H3 H4]. subst. simpl in H1.
      rewrite map.putmany_comm by assumption.
      eapply oldexec.weaken.
      + eapply H1; [assumption|]. constructor; [assumption|]. apply all_disj_alt_conv.
        apply map.disjoint_comm. assumption.
      + simpl. intros. fwd. inversion H3p1. subst. clear H3p1. subst.
        do 2 eexists. intuition eauto.
        -- apply map.split_comm.
           simpl. split; [reflexivity|].
           eapply map.sub_domain_disjoint. 2: apply H7. apply map.disjoint_comm.
           eapply map.sub_domain_disjoint. 1: eassumption.
           apply same_domain_flattened. assumption.
    - econstructor. 1: eapply IHexec; assumption. clear IHexec.
      simpl. intros. fwd. eapply oldexec.weaken.
      + apply H1; [assumption|]. eapply same_domain_disj; eassumption.
      + simpl. intros. fwd. eexists. intuition eauto.
        eapply same_domain_trans; eassumption.
    - eapply oldexec.while_true; eauto. simpl. intros. fwd. eapply oldexec.weaken.
      + apply H3; [assumption|]. eapply same_domain_disj; eassumption.
      + simpl. intros. fwd. eexists. intuition eauto.
        eapply same_domain_trans; eassumption.
    - econstructor; eauto. simpl. intros. fwd. apply H3 in H4p2. clear H3. fwd.
      eexists. intuition eauto. eexists. intuition eauto.
  Qed.

  Lemma exec_implies_oldexec e s t mi l post :
    exec e s t [mi] l post ->
    oldexec e s t mi l
      (fun t mi' l => post t [mi'] l).
  Proof.
    intros. replace mi with (fold_right map.putmany map.empty [mi]) in *.
    2: { simpl. rewrite map.putmany_empty_r. reflexivity. }
    eapply oldexec.weaken.
    - eapply exec_implies_oldexec'.
      + constructor; [constructor|]. intros _ [].
      + simpl in H. rewrite map.putmany_empty_r in H. eassumption.
    - simpl. intros. fwd. inversion H0p1. subst. inversion H4. subst. simpl.
      rewrite map.putmany_empty_r. assumption.
  Qed.

  Print cmd.
  Open Scope bool_scope.
  
  Fixpoint some_dce (s : cmd) :=
    match s with
    | cmd.stackalloc x n cmd.skip => if Z.leb 0 n && Z.leb n (Z.pow 2 width) then cmd.set x (expr.literal 0) else s
    | cmd.stackalloc x n body => cmd.stackalloc x n (some_dce body)
    | cmd.cond c i e => cmd.cond c (some_dce i) (some_dce e)
    | cmd.seq s1 s2 => cmd.seq (some_dce s1) (some_dce s2)
    | cmd.while c body => cmd.while c (some_dce body)
    | _ => s
    end.
  
  Lemma anybytes_exist n base :
    le n (Z.to_nat (Z.pow 2 width - Z.of_nat base)) ->
    anybytes (@word.of_Z width word (Z.of_nat base)) (Z.of_nat n)
      (OfFunc.map.of_func (fun (_ : word) => Some Byte.x00) (map (fun x => word.of_Z (Z.of_nat x)) (seq base n))).
  Proof.
    intros. eassert (Z.of_nat n = _) as ->.
    2: { eapply array_1_to_anybytes. instantiate (1 := repeat Byte.x00 n).
         revert base H. induction n.
         - simpl. split; reflexivity.
         - intros. simpl. cbv [Separation.sep]. eexists. eexists. split; [|split].
           3: { replace (word.add (word.of_Z (Z.of_nat base)) (word.of_Z 1)) with (@word.of_Z width word (Z.of_nat (S base))).
                - apply IHn. lia.
                - rewrite <- Properties.word.ring_morph_add. f_equal. lia. }
           2: { reflexivity. }
           split.
           + apply map.map_ext. intros.
             rewrite map.get_put_dec. destruct_one_match.
             -- rewrite map.get_putmany_left.
                ++ rewrite map.get_put_same. reflexivity.
                ++ apply OfFunc.map.get_of_func_notIn.
                   intros H'. apply in_map_iff in H'. fwd. apply in_seq in H'p1.
                   pose proof @Properties.word.of_Z_inj_small width word word_ok as P.
                   specialize P with (1 := H'p0).
                   specialize (P ltac:(lia) ltac:(lia)). clear H'p0. lia.
             -- rewrite map.get_putmany_dec. destruct_one_match; [reflexivity|].
                rewrite map.get_put_diff by auto. rewrite map.get_empty. reflexivity.
           + apply map.disjoint_put_l. 2: apply map.disjoint_empty_l.
             apply OfFunc.map.get_of_func_notIn.
                   intros H'. apply in_map_iff in H'. fwd. apply in_seq in H'p1.
                   pose proof @Properties.word.of_Z_inj_small width word word_ok as P.
                   specialize P with (1 := H'p0).
                   specialize (P ltac:(lia) ltac:(lia)). clear H'p0. lia. }
    rewrite repeat_length. Check length_rev. (*this should be the same as length_rev...*)
    reflexivity.
  Qed.    
  
  Lemma some_dce_correct e s t m l post :
    exec e s t m l post ->
    exec e (some_dce s) t m l post.
  Proof.
    intros H. induction H; try solve [econstructor; eauto].
    destruct body; try solve [econstructor; eauto].
    clear H0. simpl in H1. pose proof (anybytes_exist (Z.to_nat n) 0) as somebytes.
    simpl. destruct (Z.leb 0 n && (n <=? 2 ^ width)) eqn:E; [|solve [econstructor; eauto]].
    apply andb_prop in E. destruct E as [E1 E2]. apply Z.leb_le in E1, E2.
    specialize (somebytes ltac:(lia)).
    rewrite Znat.Z2Nat.id in somebytes by lia.
    specialize H1 with (1 := somebytes). inversion H1. clear H1. subst. fwd.
    econstructor. 1: reflexivity. assumption.
  Qed.
End WithParams.
