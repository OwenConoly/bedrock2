Require Import coqutil.sanity coqutil.Macros.subst coqutil.Macros.unique coqutil.Byte.
Require Import coqutil.Datatypes.PrimitivePair coqutil.Datatypes.HList.
Require Import coqutil.Decidable.
Require Import coqutil.Tactics.fwd.
Require Import coqutil.Map.Properties.
Require Import bedrock2.Syntax coqutil.Map.Interface coqutil.Map.OfListWord.
Require Import BinIntDef coqutil.Word.Interface coqutil.Word.Bitwidth.
Require Import bedrock2.MetricLogging.
Require Export bedrock2.Memory.

Require Import Coq.Lists.List.

(* BW is not needed on the rhs, but helps infer width *)
Definition io_input {width: Z}{BW: Bitwidth width}{word: word.word width}{mem: map.map word byte} : Type :=
  (mem * String.string * list word).
Definition io_output {width: Z}{BW: Bitwidth width}{word: word.word width}{mem: map.map word byte} : Type :=
  (mem * list word).

Section WithIOEvent.
  Context {width: Z}{BW: Bitwidth width}{word: word.word width}{mem: map.map word byte}.

  Definition io_event : Type := io_input * io_output.
  Definition io_trace : Type := list io_event.

  Inductive abstract_trace : Type :=
  | empty
  | cons_IO (e: io_input) (after : io_output -> abstract_trace)
  | cons_branch (b : bool) (after : abstract_trace)
  | cons_read (sz : access_size) (a : word) (after : abstract_trace)
  | cons_write (sz : access_size) (a : word) (after : abstract_trace)
  | cons_salloc (after : word -> abstract_trace).

  Definition with_IO e := option_map (cons_IO e).
  Lemma with_IO_inj e e' a a' : with_IO e a = with_IO e' a' -> a = a'.
  Proof. intros H. destruct a; destruct a'; simpl in H; congruence. Qed.
  
  Definition with_branch b := option_map (cons_branch b).
  Lemma with_branch_inj b b' a a' : with_branch b a = with_branch b' a' -> a = a'.
  Proof. intros. destruct a; destruct a'; simpl in H; congruence. Qed.
  
  Definition with_read sz addr := option_map (cons_read sz addr).
  Lemma with_read_inj sz addr addr' a a' : with_read sz addr a = with_read sz addr' a' -> a = a'.
  Proof. intros. destruct a; destruct a'; simpl in H; congruence. Qed.
  
  Definition with_write sz addr := option_map (cons_write sz addr).
  Lemma with_write_inj sz addr addr' a a' : with_write sz addr a = with_write sz addr' a' -> a = a'.
  Proof. intros. destruct a; destruct a'; simpl in H; congruence. Qed.
  Lemma with_write_ct sz addr a a' : cons_write sz addr a' = a -> with_write sz addr (Some a') = Some a.
  Proof. intros. simpl. f_equal. assumption. Qed.
  Lemma with_write_nct sz addr : with_write sz addr None = None.
  Proof. reflexivity. Qed.
  Lemma cons_write_fun sz addr a : cons_write sz addr a = cons_write sz addr a.
  Proof. reflexivity. Qed.

  Definition with_salloc := option_map cons_salloc.
  Lemma with_salloc_inj a a' : with_salloc a = with_salloc a' -> a = a'.
  Proof. intros. destruct a; destruct a'; simpl in H; congruence. Qed.

  Definition apply_salloc (f : option (word -> abstract_trace)) addr :=
    match f with | Some f => Some (f addr) | None => None end.
  Definition apply_IO (f : option (io_output -> abstract_trace)) i :=
    match f with | Some f => Some (f i) | None => None end.

  Definition pop_read a s addr : option (option abstract_trace) :=
    match a with
    | Some (cons_read s0 addr0 a') =>
        if (access_size.access_size_beq s s0 && word.eqb addr addr0)%bool
        then
          Some (Some a')
        else None
    | None => Some None
    | _ => None end.
  
  Definition pop_branch a b : option (option abstract_trace) :=
    match a with
    | Some (cons_branch b0 a') =>
        if (Bool.eqb b b0)%bool
        then
          Some (Some a')
        else None
    | None => Some None
    | _ => None end.
End WithIOEvent.

  Definition ExtSpec{width: Z}{BW: Bitwidth width}{word: word.word width}{mem: map.map word byte} :=
  (* Given a trace of what happened so far,
     the given-away memory, an action label and a list of function call arguments, *)
  io_trace -> mem -> String.string -> list word ->
  (* and a postcondition on the received memory and function call results, *)
  (mem -> list word -> Prop) ->
  (* tells if this postcondition will hold *)
  Prop.

Existing Class ExtSpec.

Module ext_spec.
  Class ok{width: Z}{BW: Bitwidth width}{word: word.word width}{mem: map.map word byte}
          {ext_spec: ExtSpec}: Prop :=
  {
    (* The action name and arguments uniquely determine the footprint of the given-away memory. *)
    unique_mGive_footprint: forall t1 t2 mGive1 mGive2 a args
                                            (post1 post2: mem -> list word -> Prop),
        ext_spec t1 mGive1 a args post1 ->
        ext_spec t2 mGive2 a args post2 ->
        map.same_domain mGive1 mGive2;

    weaken :> forall t mGive act args,
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

Section semantics.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word byte}.
  Context {locals: map.map String.string word}.
  Context {env: map.map String.string (list String.string * list String.string * cmd)}.
  Context {ext_spec: ExtSpec}.

  Local Notation metrics := MetricLog.

  (* this is the expr evaluator that is used to verify execution time, the just-correctness-oriented version is below *)
  Section WithMemAndLocals.
    Context (m : mem) (l : locals).
    Local Notation "' x <- a | y ; f" := (match a with x => f | _ => y end)
                                           (right associativity, at level 70, x pattern).
    Fixpoint eval_expr (e : expr) (mc : metrics) (a : option abstract_trace) : option (word * metrics * option abstract_trace) :=
      match e with
      | expr.literal v => Some (
                              word.of_Z v,
                              addMetricInstructions 8 (addMetricLoads 8 mc),
                              a)
      | expr.var x => match map.get l x with
                      | Some v => Some (
                                      v,
                                      addMetricInstructions 1 (addMetricLoads 2 mc),
                                      a)
                      | None => None
                      end
      (* if i understand correctly, this thing does not access memory at all.
         so no change to leakage trace. *)
      | expr.inlinetable aSize t index =>
          'Some (index', mc', a') <- eval_expr index mc a | None;
          'Some v <- load aSize (map.of_list_word t) index' | None;
          Some (
              v,
              (addMetricInstructions 3 (addMetricLoads 4 (addMetricJumps 1 mc'))),
              a')
      | expr.load aSize addr =>
          'Some (addr', mc', a') <- eval_expr addr mc a | None;
          'Some v <- load aSize m addr' | None;
          'Some a'' <- pop_read a' aSize addr' | None;
          Some (
              v,
              addMetricInstructions 1 (addMetricLoads 2 mc'),
              a'')
      | expr.op op e1 e2 =>
          'Some (v1, mc', a') <- eval_expr e1 mc a | None;
          'Some (v2, mc'', a'') <- eval_expr e2 mc' a' | None;
          Some (
              interp_binop op v1 v2,
              addMetricInstructions 2 (addMetricLoads 2 mc''),
              a'')
      | expr.ite c e1 e2 =>
          'Some (vc, mc', a') <- eval_expr c mc a | None;
          'Some a'' <- pop_branch a' (negb (word.eqb vc (word.of_Z 0))) | None;
          eval_expr
            (if word.eqb vc (word.of_Z 0) then e2 else e1)
            (addMetricInstructions 2 (addMetricLoads 2 (addMetricJumps 1 mc')))
            a''
      end.

    Fixpoint eval_expr_old (e : expr) : option word :=
      match e with
      | expr.literal v => Some (word.of_Z v)
      | expr.var x => map.get l x
      | expr.inlinetable aSize t index =>
          'Some index' <- eval_expr_old index | None;
          load aSize (map.of_list_word t) index'
      | expr.load aSize a =>
          'Some a' <- eval_expr_old a | None;
          load aSize m a'
      | expr.op op e1 e2 =>
          'Some v1 <- eval_expr_old e1 | None;
          'Some v2 <- eval_expr_old e2 | None;
          Some (interp_binop op v1 v2)
      | expr.ite c e1 e2 =>
          'Some vc <- eval_expr_old c | None;
          eval_expr_old (if word.eqb vc (word.of_Z 0) then e2 else e1)
    end.

    Fixpoint evaluate_call_args_log (arges : list expr) (mc : metrics) (a : option abstract_trace) :=
      match arges with
      | e :: tl =>
        'Some (v, mc', a') <- eval_expr e mc a | None;
        'Some (args, mc'', a'') <- evaluate_call_args_log tl mc' a' | None;
        Some (v :: args, mc'', a'')
      | _ => Some (nil, mc, a)
      end.

  End WithMemAndLocals.
End semantics.

Module exec. Section WithEnv.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word byte}.
  Context {locals: map.map String.string word}.
  Context {env: map.map String.string (list String.string * list String.string * cmd)}.
  Context {ext_spec: ExtSpec}.
  Context (e: env).

  Local Notation metrics := MetricLog.

  Implicit Types post : io_trace -> mem -> locals -> metrics -> option abstract_trace -> Prop. (* COQBUG(unification finds Type instead of Prop and fails to downgrade *)
  
  Inductive exec :
    cmd -> io_trace -> mem -> locals -> metrics -> option abstract_trace ->
    (io_trace -> mem -> locals -> metrics -> option abstract_trace -> Prop) -> Prop :=
  | skip
    t m l mc a post
    (_ : post t m l mc a)
    : exec cmd.skip t m l mc a post
  | set x e
    t m l mc a post
    v mc' a' (_ : eval_expr m l e mc a = Some (v, mc', a'))
    (_ : post t m (map.put l x v) (addMetricInstructions 1
                                     (addMetricLoads 1 mc')) a')
    : exec (cmd.set x e) t m l mc a post
  | unset x
    t m l mc a post
    (_ : post t m (map.remove l x) mc a)
    : exec (cmd.unset x) t m l mc a post
  | store sz ea ev
    t m l mc a post
    addr mc' a' (_ : eval_expr m l ea mc a = Some (addr, mc', a'))
    v mc'' a'' (_ : eval_expr m l ev mc' a' = Some (v, mc'', (with_write sz addr a'')))
    m' (_ : store sz m addr v = Some m')
    (_ : post t m' l (addMetricInstructions 1
                        (addMetricLoads 1
                           (addMetricStores 1 mc''))) a'')
    : exec (cmd.store sz ea ev) t m l mc a post
  | stackalloc x n body
    t mSmall l mc f post
    (_ : Z.modulo n (bytes_per_word width) = 0)
    (_ : forall addr mStack mCombined,
        anybytes addr n mStack ->
        map.split mCombined mSmall mStack ->
        exec body t mCombined (map.put l x addr) (addMetricInstructions 1 (addMetricLoads 1 mc)) (apply_salloc f addr)
          (fun t' mCombined' l' mc' a' =>
             exists mSmall' mStack',
              anybytes addr n mStack' /\
              map.split mCombined' mSmall' mStack' /\
              post t' mSmall' l' mc' a'))
    : exec (cmd.stackalloc x n body) t mSmall l mc (with_salloc f) post
  | if_true t m l mc e c1 c2 a a' post
    v mc' (_ : eval_expr m l e mc a = Some (v, mc', (with_branch true a')))
    (_ : word.unsigned v <> 0)
    (_ : exec c1 t m l (addMetricInstructions 2
                          (addMetricLoads 2
                             (addMetricJumps 1 mc'))) a' post)
    : exec (cmd.cond e c1 c2) t m l mc a post
  | if_false e c1 c2
    t m l mc a a' post
    v mc' (_ : eval_expr m l e mc a = Some (v, mc', with_branch false a'))
    (_ : word.unsigned v = 0)
    (_ : exec c2 t m l (addMetricInstructions 2
                          (addMetricLoads 2
                             (addMetricJumps 1 mc'))) a' post)
    : exec (cmd.cond e c1 c2) t m l mc a post
  | seq c1 c2
    t m l mc a post
    mid (_ : exec c1 t m l mc a mid)
    (_ : forall t' m' l' mc' a', mid t' m' l' mc' a' -> exec c2 t' m' l' mc' a' post)
    : exec (cmd.seq c1 c2) t m l mc a post
  | while_false e c
    t m l mc a a' post
    v mc' (_ : eval_expr m l e mc a = Some (v, mc', (with_branch false a')))
    (_ : word.unsigned v = 0)
    (_ : post t m l (addMetricInstructions 1
                       (addMetricLoads 1
                          (addMetricJumps 1 mc'))) a')
    : exec (cmd.while e c) t m l mc a post
  | while_true e c
      t m l mc a post
      v mc' a' (_ : eval_expr m l e mc a = Some (v, mc', with_branch true a'))
      (_ : word.unsigned v <> 0)
      mid (_ : exec c t m l mc' a' mid)
      (_ : forall t' m' l' mc'' a', mid t' m' l' mc'' a' ->
                                    exec (cmd.while e c) t' m' l' (addMetricInstructions 2
                                                                     (addMetricLoads 2
                                                                        (addMetricJumps 1 mc''))) a' post)
    : exec (cmd.while e c) t m l mc a post
  | call binds fname arges
      t m l mc a post
      params rets fbody (_ : map.get e fname = Some (params, rets, fbody))
      args mc' a' (_ : evaluate_call_args_log m l arges mc a = Some (args, mc', a'))
      lf (_ : map.of_list_zip params args = Some lf)
      mid (_ : exec fbody t m lf (addMetricInstructions 100 (addMetricJumps 100 (addMetricLoads 100 (addMetricStores 100 mc')))) a' mid)
      (_ : forall t' m' st1 mc'' a', mid t' m' st1 mc'' a' ->
          exists retvs, map.getmany_of_list st1 rets = Some retvs /\
          exists l', map.putmany_of_list_zip binds retvs l = Some l' /\
          post t' m' l' (addMetricInstructions 100 (addMetricJumps 100 (addMetricLoads 100 (addMetricStores 100 mc'')))) a')
    : exec (cmd.call binds fname arges) t m l mc a post
  | interact binds action arges
      t m l mc a post
      mKeep mGive (_: map.split m mKeep mGive)
      args mc' f (_ :  evaluate_call_args_log m l arges mc a = Some (args, mc', with_IO (mGive, action, args) f))
      mid (_ : ext_spec t mGive action args mid)
      (_ : forall mReceive resvals, mid mReceive resvals ->
          exists l', map.putmany_of_list_zip binds resvals l = Some l' /\
          forall m', map.split m' mKeep mReceive ->
          post (((mGive, action, args), (mReceive, resvals)) :: t) m' l'
            (addMetricInstructions 1
            (addMetricStores 1
            (addMetricLoads 2 mc'))) (apply_IO f (mReceive, resvals)))
    : exec (cmd.interact binds action arges) t m l mc a post
  .

  Context {word_ok: word.ok word} {mem_ok: map.ok mem} {ext_spec_ok: ext_spec.ok ext_spec}.

  Lemma weaken: forall t l m mc a s post1,
      exec s t m l mc a post1 ->
      forall post2: _ -> _ -> _ -> _ -> _ -> Prop,
        (forall t' m' l' mc' a', post1 t' m' l' mc' a' -> post2 t' m' l' mc' a') ->
        exec s t m l mc a post2.
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

  Lemma intersect: forall t l m mc a s post1,
      exec s t m l mc a post1 ->
      forall post2,
        exec s t m l mc a post2 ->
        exec s t m l mc a (fun t' m' l' mc' a' => post1 t' m' l' mc' a' /\ post2 t' m' l' mc' a').
  Proof.
    induction 1;
      intros;
      match goal with
      | H: exec _ _ _ _ _ _ _ |- _ => inversion H; subst; clear H
      end;
      repeat match goal with
      | H1: ?e = Some (?v1, ?mc1, ?t1), H2: ?e = Some (?v2, ?mc2, ?t2) |- _ =>
          rewrite H1 in H2; injection H2 as H2p1 H2p2 H2p3; subst end;
      repeat match goal with
      | H1: ?e = Some ?v1, H2: ?e = Some ?v2 |- _ =>
          replace v2 with v1 in * by congruence; clear H2
      end;
      try match goal with
        | H : with_write _ _ _ = with_write _ _ _ |- _ => apply with_write_inj in H; subst
        | H : with_salloc _ = with_salloc _ |- _ => apply with_salloc_inj in H; subst
        | H : with_branch _ _ = with_branch _ _ |- _ => apply with_branch_inj in H; subst
        | H : with_IO _ _ = with_IO _ _ |- _ => apply with_IO_inj in H; subst
      end;
      try solve [econstructor; eauto | exfalso; congruence].
    - econstructor. 1: eassumption.
      intros.
      rename H0 into Ex1, H13 into Ex2.
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
      + eapply IHexec. exact H17. (* not H2 *)
      + simpl. intros *. intros [? ?].
        edestruct H3 as (? & ? & ? & ? & ?); [eassumption|].
        edestruct H18 as (? & ? & ? & ? & ?); [eassumption|].
        repeat match goal with
               | H1: ?e = Some ?v1, H2: ?e = Some ?v2 |- _ =>
                 replace v2 with v1 in * by congruence; clear H2
               end.
        eauto 10.
    - pose proof ext_spec.unique_mGive_footprint as P.
      specialize P with (1 := H1) (2 := H15).
      destruct (map.split_diff P H H7). subst mKeep0 mGive0. clear H7.
      eapply interact. 1,2: eassumption.
      + eapply ext_spec.intersect; [ exact H1 | exact H15 ].
      + simpl. intros *. intros [? ?].
        edestruct H2 as (? & ? & ?); [eassumption|].
        edestruct H16 as (? & ? & ?); [eassumption|].
        repeat match goal with
               | H1: ?e = Some ?v1, H2: ?e = Some ?v2 |- _ =>
                 replace v2 with v1 in * by congruence; clear H2
               end.
        eauto 10.
  Qed.

  End WithEnv.
End exec. Notation exec := exec.exec.
