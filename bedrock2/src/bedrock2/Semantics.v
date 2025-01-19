Require Import coqutil.sanity coqutil.Byte.
Require Import coqutil.Tactics.fwd coqutil.Tactics.Tactics.
Require Import coqutil.Map.Properties.
Require coqutil.Map.SortedListString.
Require Import bedrock2.Syntax coqutil.Map.Interface coqutil.Map.OfListWord.
Require Import BinIntDef coqutil.Word.Interface coqutil.Word.Bitwidth.
Require Export bedrock2.Memory.
Require Import Coq.Lists.List.
Import ListNotations.

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
                     map.disjoint mi (fold_right map.putmany map.empty m) ->
                     all_disj (mi :: m).

  Lemma all_disj_alt mi m :
    all_disj (mi :: m) ->
    forall mj, In mj m ->
          map.disjoint mi mj.
  Proof. Admitted.

  Lemma all_disj_putmany_commute m :
    all_disj m ->
    fold_right map.putmany map.empty m = fold_right (fun x y => map.putmany y x) map.empty m.
  Proof.
    induction m; intros Hdisj; [reflexivity|]. inversion Hdisj. subst.
    specialize (IHm ltac:(assumption)). simpl. rewrite <- IHm. apply map.putmany_comm.
    assumption.
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
      + Search (map.get (map.putmany _ _)). apply map.get_putmany_right. assumption.
      + rewrite map.get_putmany_left.
        -- apply IHm; assumption.
        -- pose proof all_disj_alt as H'. specialize (H' _ _ Hdisj _ H).
           clear -H' Hget. cbv [map.disjoint] in H'. specialize (H' a).
           destruct (map.get a0 a); [|reflexivity]. exfalso. eapply H'; eauto.
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
  
  Lemma exec_implies_oldexec e s t m l post :
    all_disj m ->
    exec e s t m l post ->
    oldexec e s t (fold_right map.putmany map.empty m) l
      (fun t mflat' l =>
         exists m', mflat' = fold_right map.putmany map.empty m' /\
         post t m' l).
  Proof.
    intros H0 H. revert H0. induction H; intros Hdisj; try solve [econstructor; eauto].
    - econstructor; eauto using all_disj_load.
    - econstructor; eauto.

      
                
    
    
    
    
End WithParams.
