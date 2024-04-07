Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Wellfounded.Transitive_Closure.
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

(* not sure where to put these lemmas *)
Lemma align_trace_cons {T} x xs cont t (H : xs = List.app cont t) : @List.cons T x xs = List.app (cons x cont) t.
Proof. intros. cbn. congruence. Qed.
Lemma align_trace_app {T} x xs cont t (H : xs = List.app cont t) : @List.app T x xs = List.app (List.app x cont) t.
Proof. intros. cbn. subst. rewrite List.app_assoc; trivial. Qed.

Ltac trace_alignment :=
  repeat match goal with
    | t := cons _ _ |- _ => subst t
    end;
  repeat (eapply align_trace_app
          || eapply align_trace_cons
          || exact (eq_refl (List.app nil _))).

Lemma app_one_l {A} (a : A) l : (a :: l = (cons a nil) ++ l)%list.
Proof. reflexivity. Qed.

(* BW is not needed on the rhs, but helps infer width *)
Definition io_event {width: Z}{BW: Bitwidth width}{word: word.word width}{mem: map.map word byte} : Type :=
  (mem * String.string * list word) * (mem * list word).

(*could reduce this to many fewer cases, at the cost of being a bit more confusing.*)
(*actually no, it wouldn't even be that confusing.  It's very tempting to just let
event := bool | word | unit. *)
(*should I name this leakage_event, now that it doesn't contain the IO events?*)
Inductive event {width: Z}{BW: Bitwidth width}{word: word.word width} : Type :=
| leak_unit : event
| leak_bool : bool -> event
| leak_word : word -> event
| leak_list : list word -> event.
(* ^we need this, because sometimes it's convenient that one io call leaks only one event
   See Interact case of spilling transform_trace function for an example. *)
(*This looks pretty, but it seems hard to work with.  Can't even use the inversion tactic?
Inductive event : Type :=
| leak : forall {A : Type}, A -> event
| consume : forall {A : Type}, A -> event.*)

Section WithIOEvent.
  Context {width: Z}{BW: Bitwidth width}{word: word.word width}{mem: map.map word byte}.

  (*should I call this leakage_trace, now that it doesn't contain io events?
    shame to lengthen the name. No, I shouldn't call it a leakage trace, since 
    it contains the sources of nondeterminism as well as leakage events.*)
  Definition trace : Type := list event.
  Definition io_trace : Type := list io_event.
End WithIOEvent. (*maybe extend this to the end?*)
                            
  Definition ExtSpec{width: Z}{BW: Bitwidth width}{word: word.word width}{mem: map.map word byte} :=
  (* Given a trace of what happened so far,
     the given-away memory, an action label and a list of function call arguments, *)
  io_trace -> mem -> String.string -> list word ->
  (* and a postcondition on the received memory, function call results, and leakage trace, *)
  (mem -> list word -> list word -> Prop) ->
  (* tells if this postcondition will hold *)
  Prop.

Existing Class ExtSpec.

Module ext_spec.
  Class ok{width: Z}{BW: Bitwidth width}{word: word.word width}{mem: map.map word byte}
          {ext_spec: ExtSpec}: Prop :=
  {
    (* The action name and arguments uniquely determine the footprint of the given-away memory. *)
    unique_mGive_footprint: forall t1 t2 mGive1 mGive2 a args
                                   (post1 post2: mem -> list word -> list word -> Prop),
        ext_spec t1 mGive1 a args post1 ->
        ext_spec t2 mGive2 a args post2 ->
        map.same_domain mGive1 mGive2;

    weaken :> forall t mGive act args,
        Morphisms.Proper
          (Morphisms.respectful
             (Morphisms.pointwise_relation Interface.map.rep
                (Morphisms.pointwise_relation (list word)
                   (Morphisms.pointwise_relation (list word) Basics.impl))) Basics.impl)
          (ext_spec t mGive act args);

    intersect: forall t mGive a args
                      (post1 post2: mem -> list word -> list word -> Prop),
        ext_spec t mGive a args post1 ->
        ext_spec t mGive a args post2 ->
        ext_spec t mGive a args (fun mReceive resvals klist =>
                                   post1 mReceive resvals klist /\ post2 mReceive resvals klist);
  }.
End ext_spec.
Arguments ext_spec.ok {_ _ _ _} _.

(*Definition PickSp {width: Z}{BW: Bitwidth width}{word: word.word width}{mem: map.map word byte} : Type :=
  trace -> word.
Existing Class PickSp.*)

Section binops.
  Context {width : Z} {BW: Bitwidth width} {word : Word.Interface.word width}.
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
  Definition leak_binop (bop : bopname) (x1 : word) (x2 : word) : trace :=
    match bop with
    | bopname.divu | bopname.remu => cons (leak_word x2) (cons (leak_word x1) nil)
    | bopname.sru | bopname.slu | bopname.srs => cons (leak_word x2) nil
    | _ => nil
    end.
End binops.

Section semantics.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word byte}.
  Context {locals: map.map String.string word}.
  Context {env: map.map String.string (list String.string * list String.string * cmd)}.

  Local Notation metrics := MetricLog.

  (* this is the expr evaluator that is used to verify execution time, the just-correctness-oriented version is below *)
  Section WithMemAndLocals.
    Context (m : mem) (l : locals).

    Local Notation "' x <- a | y ; f" := (match a with x => f | _ => y end)
                                           (right associativity, at level 70, x pattern).
    Fixpoint eval_expr (e : expr) (mc : metrics) (tr : trace) : option (word * metrics * trace) :=
      match e with
      | expr.literal v => Some (
                              word.of_Z v,
                              addMetricInstructions 8 (addMetricLoads 8 mc),
                              tr)
      | expr.var x => match map.get l x with
                      | Some v => Some (
                                      v,
                                      addMetricInstructions 1 (addMetricLoads 2 mc),
                                      tr)
                      | None => None
                      end
      | expr.inlinetable aSize t index =>
          'Some (index', mc', tr') <- eval_expr index mc tr | None;
          'Some v <- load aSize (map.of_list_word t) index' | None;
          Some (
              v,
              (addMetricInstructions 3 (addMetricLoads 4 (addMetricJumps 1 mc'))),
              leak_word index' :: tr')
      | expr.load aSize a =>
          'Some (a', mc', tr') <- eval_expr a mc tr | None;
          'Some v <- load aSize m a' | None;
          Some (
              v,
              addMetricInstructions 1 (addMetricLoads 2 mc'),
              leak_word a' :: tr')
      | expr.op op e1 e2 =>
          'Some (v1, mc', tr') <- eval_expr e1 mc tr | None;
          'Some (v2, mc'', tr'') <- eval_expr e2 mc' tr' | None;
          Some (
              interp_binop op v1 v2,
              addMetricInstructions 2 (addMetricLoads 2 mc''),
              leak_binop op v1 v2 ++ tr'')
      | expr.ite c e1 e2 =>
          'Some (vc, mc', tr') <- eval_expr c mc tr | None;
          eval_expr
            (if word.eqb vc (word.of_Z 0) then e2 else e1)
            (addMetricInstructions 2 (addMetricLoads 2 (addMetricJumps 1 mc')))
            ((if word.eqb vc (word.of_Z 0) then leak_bool false else leak_bool true) :: tr')
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

    Fixpoint evaluate_call_args_log (arges : list expr) (mc : metrics) (tr : trace) :=
      match arges with
      | e :: tl =>
          'Some (v, mc', tr') <- eval_expr e mc tr | None;
          'Some (args, mc'', tr'') <- evaluate_call_args_log tl mc' tr' | None;
          Some (v :: args, mc'', tr'')
      | _ => Some (nil, mc, tr)
    end.

    Lemma expr_to_other_trace e mc mc' k1 k1' v :
      eval_expr e mc k1 = Some (v, mc', k1') ->
      exists k'',
        k1' = k'' ++ k1 /\
          forall k2,
          eval_expr e mc k2 = Some (v, mc', k'' ++ k2).
    Proof.
      revert v. revert mc. revert k1. revert k1'. revert mc'. clear.
      induction e; intros ? ? ? ? ? H; simpl in H; try (inversion H; subst; clear H).
      - exists nil. auto.
      - destruct (map.get l x) as [v0|] eqn:E; [|congruence]. inversion H1; subst; clear H1.
        exists nil. simpl. rewrite E. auto.
      - destruct (eval_expr _ _ _) as [v0|] eqn:E1; [|congruence].
        destruct v0. destruct p. destruct (load _ _ _) as [v0|] eqn:E2; [|congruence].
        inversion H1; subst; clear H1. eapply IHe in E1. destruct E1 as [k'' [E1 E3] ]. subst.
        eexists (_ :: _). intuition. simpl. rewrite E3. rewrite E2. reflexivity.
      - destruct (eval_expr _ _ _) as [v0|] eqn:E1; [|congruence].
        destruct v0. destruct p. destruct (load _ _ _) as [v0|] eqn:E2; [|congruence].
        inversion H1; subst; clear H1. eapply IHe in E1. destruct E1 as [k'' [E1 E3] ]. subst.
        eexists (_ :: _). intuition. simpl. rewrite E3. rewrite E2. reflexivity.
      - destruct (eval_expr e1 _ _) as [ [ [v0 mc0] p0]|] eqn:E1; [|congruence].
        destruct (eval_expr e2 _ _) as [ [ [v1 mc1] p1]|] eqn:E2; [|congruence].
        inversion H1; subst; clear H1.
        eapply IHe1 in E1. destruct E1 as [k''1 [H1 H2] ]. eapply IHe2 in E2.
        destruct E2 as [k''2 [H3 H4] ]. subst.
        eexists (_ ++ _ ++ _). repeat rewrite <- (app_assoc _ _ k1). intuition.
        simpl. rewrite H2. rewrite H4. f_equal. f_equal. repeat rewrite <- (app_assoc _ _ k2).
        reflexivity.
      - destruct (eval_expr e1 _ _) as [ [ [v0 mc0] p0]|] eqn:E1; [|congruence].
        eapply IHe1 in E1. destruct E1 as [k''1 [H2 H3] ]. subst. simpl.
        destruct (word.eqb _ _) eqn:E.
        + eapply IHe3 in H1. destruct H1 as [k''3 [H1 H2] ]. subst.
          eexists (_ ++ _ :: _). repeat rewrite <- (app_assoc _ _ k1).
          intuition. rewrite H3. rewrite E. rewrite H2.
          repeat rewrite <- (app_assoc _ _ k2). reflexivity.
        + eapply IHe2 in H1. destruct H1 as [k''2 [H1 H2] ]. subst.
          eexists (_ ++ _ :: _). repeat rewrite <- (app_assoc _ _ k1).
          intuition. rewrite H3. rewrite E. rewrite H2.
          repeat rewrite <- (app_assoc _ _ k2). reflexivity.
    Qed.

    Lemma call_args_to_other_trace arges mc k1 vs mc' k1' :
      evaluate_call_args_log arges mc k1 = Some (vs, mc', k1') ->
      exists k'',
        k1' = k'' ++ k1 /\
          forall k2,
            evaluate_call_args_log arges mc k2 = Some (vs, mc', k'' ++ k2).
    Proof.
      revert mc. revert k1. revert vs. revert mc'. revert k1'. induction arges; intros.
      - cbn [evaluate_call_args_log] in H. inversion H. subst.
        exists nil. intuition.
      - cbn [evaluate_call_args_log] in *.
        destruct (eval_expr _ _ _) as [ [ [v0 mc0] p0]|] eqn:E1; [|congruence].
        destruct (evaluate_call_args_log _ _ _) as [ [ [v1 mc1] p1]|] eqn:E2; [|congruence].
        apply expr_to_other_trace in E1. apply IHarges in E2. fwd.
        eexists (_ ++ _).
        repeat rewrite <- (app_assoc _ _ k1). intuition. repeat rewrite <- (app_assoc _ _ k2).
        rewrite E1p1. rewrite E2p1. reflexivity.
    Qed.
    
  End WithMemAndLocals.
End semantics.

Definition PickSp {width: Z}{BW: Bitwidth width}{word: word.word width}{mem: map.map word byte} : Type :=
  trace -> word.
Existing Class PickSp.

Module exec. Section WithEnv.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word byte}.
  Context {locals: map.map String.string word}.
  Context {env: map.map String.string (list String.string * list String.string * cmd)}.
  Context {ext_spec: ExtSpec}.
  Context (e: env).

  Local Notation metrics := MetricLog.

  Implicit Types post : trace -> io_trace -> mem -> locals -> metrics -> Prop. (* COQBUG(unification finds Type instead of Prop and fails to downgrade *)

  (*I really want to do the semantics like this:
    cmd -> io_trace -> mem -> locals -> metrics ->
    (trace -> io_trace -> mem -> locals -> metrics -> Prop) -> Prop.
    But it would be ugly.  Using app, screwing up simple postconditions
    (e.g., in seq case) in semantics.
    
    So I suppose I'll do 
    cmd -> trace -> io_trace -> mem -> locals -> metrics ->
    (trace -> io_trace -> mem -> locals -> metrics -> Prop) -> Prop.
    
    Then we can state a lemma, saying that exec c nil t m l mc post -> exec c k t m l mc (fun k' => post (k' ++ k)).
    Then use that wherever we want, and it's *almost* like leakage trace isn't passed as a parameter to exec.
    Still ugly though.  But better?  No, not really.  Would be horribly obnoxious to apply that lemma.  Hm.

    I suppose I had better keep the append-style for leakage traces?  :(
    Is it still worthwhile to split up the io trace and leakage trace then?
    I think so.
    It still should be less of a pain to deal with them if they're separated.
   *)
  Inductive exec {pick_sp : PickSp} :
    cmd -> trace -> io_trace -> mem -> locals -> metrics ->
    (trace -> io_trace -> mem -> locals -> metrics -> Prop) -> Prop :=
  | skip
    k t m l mc post
    (_ : post k t m l mc)
    : exec cmd.skip k t m l mc post
  | set x e
    m l mc post
    k t v mc' k' (_ : eval_expr m l e mc k = Some (v, mc', k'))
    (_ : post k' t m (map.put l x v) (addMetricInstructions 1
                                      (addMetricLoads 1 mc')))
    : exec (cmd.set x e) k t m l mc post
  | unset x
    k t m l mc post
    (_ : post k t m (map.remove l x) mc)
    : exec (cmd.unset x) k t m l mc post
  | store sz ea ev
    k t m l mc post
    a mc' k' (_ : eval_expr m l ea mc k = Some (a, mc', k'))
    v mc'' k'' (_ : eval_expr m l ev mc' k' = Some (v, mc'', k''))
    m' (_ : store sz m a v = Some m')
    (_ : post (leak_word a :: k'') t m' l (addMetricInstructions 1
                                             (addMetricLoads 1
                                                (addMetricStores 1 mc''))))
    : exec (cmd.store sz ea ev) k t m l mc post
  | stackalloc x n body
    k t mSmall l mc post
    (_ : Z.modulo n (bytes_per_word width) = 0)
    (_ : forall mStack mCombined,
        let a := pick_sp k in
        anybytes a n mStack ->
        map.split mCombined mSmall mStack ->
        exec body k t mCombined (map.put l x a) (addMetricInstructions 1 (addMetricLoads 1 mc))
          (fun k' t' mCombined' l' mc' =>
             exists mSmall' mStack',
              anybytes a n mStack' /\
              map.split mCombined' mSmall' mStack' /\
              post k' t' mSmall' l' mc'))
    : exec (cmd.stackalloc x n body) k t mSmall l mc post
  | if_true k t m l mc e c1 c2 post
    v mc' k' (_ : eval_expr m l e mc k = Some (v, mc', k'))
    (_ : word.unsigned v <> 0)
    (_ : exec c1 (leak_bool true :: k') t m l (addMetricInstructions 2 (addMetricLoads 2 (addMetricJumps 1 mc'))) post)
    : exec (cmd.cond e c1 c2) k t m l mc post
  | if_false e c1 c2
    k t m l mc post
    v mc' k' (_ : eval_expr m l e mc k = Some (v, mc', k'))
    (_ : word.unsigned v = 0)
    (_ : exec c2 (leak_bool false :: k') t m l (addMetricInstructions 2 (addMetricLoads 2 (addMetricJumps 1 mc'))) post)
    : exec (cmd.cond e c1 c2) k t m l mc post
  | seq c1 c2
    k t m l mc post
    mid (_ : exec c1 k t m l mc mid)
    (_ : forall k' t' m' l' mc', mid k' t' m' l' mc' -> exec c2 k' t' m' l' mc' post)
    : exec (cmd.seq c1 c2) k t m l mc post
  | while_false e c
    k t m l mc post
    v mc' k' (_ : eval_expr m l e mc k = Some (v, mc', k'))
    (_ : word.unsigned v = 0)
    (_ : post (leak_bool false :: k') t m l (addMetricInstructions 1
                                                (addMetricLoads 1
                                                   (addMetricJumps 1 mc'))))
    : exec (cmd.while e c) k t m l mc post
  | while_true e c
      k t m l mc post
      v mc' k' (_ : eval_expr m l e mc k = Some (v, mc', k'))
      (_ : word.unsigned v <> 0)
      mid (_ : exec c (leak_bool true :: k') t m l mc' mid)
      (_ : forall k'' t' m' l' mc'', mid k'' t' m' l' mc'' ->
                                      exec (cmd.while e c) k'' t' m' l' (addMetricInstructions 2
                                                                           (addMetricLoads 2
                                                                              (addMetricJumps 1 mc''))) post)
    : exec (cmd.while e c) k t m l mc post
  | call binds fname arges
      k t m l mc post
      params rets fbody (_ : map.get e fname = Some (params, rets, fbody))
      args mc' k' (_ : evaluate_call_args_log m l arges mc k = Some (args, mc', k'))
      lf (_ : map.of_list_zip params args = Some lf)
      mid (_ : exec fbody (leak_unit :: k') t m lf (addMetricInstructions 100 (addMetricJumps 100 (addMetricLoads 100 (addMetricStores 100 mc')))) mid)
      (_ : forall k'' t' m' st1 mc'', mid k'' t' m' st1 mc'' ->
          exists retvs, map.getmany_of_list st1 rets = Some retvs /\
          exists l', map.putmany_of_list_zip binds retvs l = Some l' /\
          post k'' t' m' l' (addMetricInstructions 100 (addMetricJumps 100 (addMetricLoads 100 (addMetricStores 100 mc'')))))
    : exec (cmd.call binds fname arges) k t m l mc post
  | interact binds action arges
      k t m l mc post
      mKeep mGive (_: map.split m mKeep mGive)
      args mc' k' (_ :  evaluate_call_args_log m l arges mc k = Some (args, mc', k'))
      mid (_ : ext_spec t mGive action args mid)
      (_ : forall mReceive resvals klist, mid mReceive resvals klist ->
          exists l', map.putmany_of_list_zip binds resvals l = Some l' /\
          forall m', map.split m' mKeep mReceive ->
          post (leak_list klist :: k')%list (((mGive, action, args), (mReceive, resvals)) :: t) m' l'
            (addMetricInstructions 1
               (addMetricStores 1
                  (addMetricLoads 2 mc'))))
    : exec (cmd.interact binds action arges) k t m l mc post
  .
  
  Context {word_ok: word.ok word} {mem_ok: map.ok mem} {ext_spec_ok: ext_spec.ok ext_spec}.

  Lemma weaken {pick_sp: PickSp} : forall s k t m l mc post1,
      exec s k t m l mc post1 ->
      forall post2: _ -> _ -> _ -> _ -> _ -> Prop,
        (forall k' t' m' l' mc', post1 k' t' m' l' mc' -> post2 k' t' m' l' mc') ->
        exec s k t m l mc post2.
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

  Lemma intersect {pick_sp: PickSp} : forall k t l m mc s post1,
      exec s k t m l mc post1 ->
      forall post2,
        exec s k t m l mc post2 ->
        exec s k t m l mc (fun k' t' m' l' mc' => post1 k' t' m' l' mc' /\ post2 k' t' m' l' mc').
  Proof.
    induction 1;
      intros;
      match goal with
      | H: exec _ _ _ _ _ _ _ |- _ => inversion H; subst; clear H
      end;
      repeat match goal with
             | H1: ?e = Some (?v1, ?mc1, ?t1), H2: ?e = Some (?v2, ?mc2, ?t2) |- _ =>
               replace v2 with v1 in * by congruence;
               replace mc2 with mc1 in * by congruence;
               replace t2 with t1 in * by congruence; clear v2 mc2 t2 H2
             end;
      repeat match goal with
             | H1: ?e = Some ?v1, H2: ?e = Some ?v2 |- _ =>
               replace v2 with v1 in * by congruence; clear H2
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

  Require Import coqutil.Z.Lia.

  Lemma eval_expr_extends_trace :
    forall e0 m l mc k v mc' k',
    eval_expr m l e0 mc k = Some (v, mc', k') ->
    exists k'', k' = k'' ++ k.
  Proof.
    intros e0. induction e0; intros; simpl in *;
      repeat match goal with
        | H: (let (_, _) := ?x in _) = _ |- _ =>
            destruct x
        | H: match ?x with
             | Some _ => _
             | None => _
             end = Some (_, _, _) |- _ =>
            destruct x eqn:?; try congruence
        | H: Some (?v1, ?mc1, ?t1) = Some (?v2, ?mc2, ?t2) |- _ =>
            injection H; intros; subst
        end.
    - eexists. trace_alignment.
    - eexists. trace_alignment.
    - specialize IHe0 with (1 := Heqo). fwd. eexists. trace_alignment.
    - specialize IHe0 with (1 := Heqo). fwd. eexists. trace_alignment.
    - specialize IHe0_1 with (1 := Heqo). specialize IHe0_2 with (1 := Heqo0). fwd.
      eexists. trace_alignment.
    - specialize IHe0_1 with (1 := Heqo). destruct (word.eqb _ _).
      + specialize IHe0_3 with (1 := H). fwd. eexists. trace_alignment.
      + specialize IHe0_2 with (1 := H). fwd. eexists. trace_alignment.
  Qed.

  Lemma evaluate_call_args_log_extends_trace :
    forall arges m l mc k args mc' k',
    evaluate_call_args_log m l arges mc k = Some (args, mc', k') ->
    exists k'', k' = k'' ++ k.
  Proof.
    intros arges. induction arges.
    - simpl. intros. injection H. intros. subst. eexists. trace_alignment.
    - simpl. intros. destruct (eval_expr _ _ _ _ _) eqn:E1; try congruence.
      destruct p. destruct p. destruct (evaluate_call_args_log _ _ _ _ _) eqn:E2; try congruence.
      destruct p. destruct p. injection H. intros. subst.
      apply eval_expr_extends_trace in E1. specialize IHarges with (1 := E2).
      fwd. eexists. trace_alignment.
  Qed.

  Local Ltac subst_exprs :=
    repeat match goal with
      | H : eval_expr _ _ _ _ _ = Some _ |- _ =>
          apply eval_expr_extends_trace in H; destruct H; subst
      | H : evaluate_call_args_log _ _ _ _ _ = Some _ |- _ =>
          apply evaluate_call_args_log_extends_trace in H; destruct H; subst
        end.

  Lemma exec_extends_trace {pick_sp: PickSp} s k t m l mc post :
    exec s k t m l mc post ->
    exec s k t m l mc (fun k' t' m' l' mc' => post k' t' m' l' mc' /\ exists k'', k' = k'' ++ k).
  Proof.
    intros H. induction H; try (econstructor; intuition eauto; subst_exprs; eexists; trace_alignment; fail).
    - econstructor; intuition eauto. intros. eapply weaken. 1: eapply H1; eauto.
      simpl. intros. fwd. eexists. eexists. intuition eauto.
    - eapply if_true; intuition eauto. eapply weaken. 1: eapply IHexec.
      simpl. intros. fwd. intuition eauto. subst_exprs. eexists. trace_alignment.
    - eapply if_false; intuition eauto. eapply weaken. 1: eapply IHexec.
      simpl. intros. fwd. intuition eauto. subst_exprs. eexists. trace_alignment.
    - econstructor; intuition eauto. fwd. eapply weaken. 1: eapply H1; eauto.
      simpl. intros. fwd. intuition eauto. eexists. trace_alignment.
    - eapply while_true; eauto. simpl. intros. fwd. eapply weaken. 1: eapply H3; eauto.
      simpl. intros. fwd. intuition eauto. subst_exprs. eexists. trace_alignment.
    - econstructor; intuition eauto. fwd. specialize H3 with (1 := H4p0). fwd.
      eexists. intuition eauto. eexists. intuition eauto. subst_exprs.
      eexists. trace_alignment.
    - econstructor; intuition eauto. specialize H2 with (1 := H3). fwd.
      eexists. intuition eauto. subst_exprs. eexists. trace_alignment.
  Qed.

  Lemma exec_ext (pick_sp1: PickSp) s k t m l mc post :
    exec (pick_sp := pick_sp1) s k t m l mc post ->
    forall pick_sp2,
    (forall k', pick_sp1 (k' ++ k) = pick_sp2 (k' ++ k)) ->
    exec (pick_sp := pick_sp2) s k t m l mc post.
  Proof.
    Set Printing Implicit.
    intros H1 pick_sp2. induction H1; intros; try solve [econstructor; eauto].
    - econstructor; eauto. intros. replace (pick_sp1 k) with (pick_sp2 k) in *.
      { subst a. eapply weaken. 1: eapply H1; eauto. simpl. eauto. }
      symmetry. apply H2 with (k' := nil).
    - eapply if_true; eauto. eapply IHexec. subst_exprs.
      intros. eassert (H2' := H2 (_ ++ _ :: _)). rewrite <- app_assoc in H2'. eapply H2'.
    - eapply if_false; eauto. eapply IHexec. subst_exprs.
      intros. eassert (H2' := H2 (_ ++ _ :: _)). rewrite <- app_assoc in H2'. eapply H2'.
    - econstructor. 1: eapply exec_extends_trace; eauto. simpl. intros. fwd.
      eapply H0; eauto. intros. repeat rewrite app_assoc. apply H2.
    - eapply while_true; intuition eauto.
      { eapply exec_extends_trace. eapply IHexec. subst_exprs.
        intros. repeat (rewrite app_assoc || rewrite (app_one_l _ (_ ++ k))). auto. }
      simpl in *. fwd. eapply H3; eauto. intros. subst_exprs.
      repeat (rewrite app_assoc || rewrite (app_one_l _ (_ ++ k))). auto.
    - econstructor. 4: eapply exec_extends_trace. all: intuition eauto.
      { eapply IHexec. subst_exprs. intros.
        repeat (rewrite app_assoc || rewrite (app_one_l _ (_ ++ k))). auto. }
      fwd. specialize H3 with (1 := H5p0). fwd. intuition eauto.
  Qed.
  
  Local Ltac solve_picksps_equal :=
    intros; cbv beta; f_equal;
    repeat (rewrite rev_app_distr || cbn [rev app]); rewrite List.skipn_app_r;
    [|repeat (rewrite app_length || rewrite rev_length || simpl); blia];
    repeat rewrite <- app_assoc; rewrite List.skipn_app_r;
    [|rewrite rev_length; reflexivity];
    repeat (rewrite rev_app_distr || cbn [rev app] || rewrite rev_involutive);
    repeat rewrite <- app_assoc; reflexivity.

  Lemma exec_to_other_trace (pick_sp: PickSp) s k1 k2 t m l mc post :
    exec s k1 t m l mc post ->
    exec (pick_sp := fun k => pick_sp (rev (skipn (length k2) (rev k)) ++ k1))
      s k2 t m l mc (fun k2' t' m' l' mc' =>
                       exists k'',
                         k2' = k'' ++ k2 /\
                           post (k'' ++ k1) t' m' l' mc').
  Proof.
    intros H. generalize dependent k2. induction H; intros.
    - econstructor. exists nil. eauto.
    - apply expr_to_other_trace in H. destruct H as [k'' [H1 H2] ]. subst.
      econstructor; intuition eauto.
    - econstructor; intuition. exists nil. intuition.
    - apply expr_to_other_trace in H. apply expr_to_other_trace in H0.
      destruct H as [k''a [H3 H4] ]. subst. destruct H0 as [k''v [H5 H6] ]. subst.
      econstructor; intuition eauto. eexists (_ :: _ ++ _). simpl.
      repeat rewrite <- (app_assoc _ _ k2). repeat rewrite <- (app_assoc _ _ k).
      intuition.
    - econstructor; intuition. intros.
      replace (rev k2) with (rev k2 ++ nil) in * by apply app_nil_r. Search (length (rev _)).
      rewrite List.skipn_app_r in * by (rewrite rev_length; reflexivity).
      simpl in *. eapply weaken. 1: eapply H1; eauto.
      simpl. intros. fwd. exists mSmall', mStack'. intuition. eauto.
    - apply expr_to_other_trace in H. fwd. eapply if_true; intuition eauto.
      eapply weaken.
      { eapply exec_ext with (pick_sp1 := _). 1: eapply IHexec. solve_picksps_equal. }
      simpl. intros. fwd. eexists (_ ++ _ :: _).
      repeat rewrite <- (app_assoc _ _ k2). repeat rewrite <- (app_assoc _ _ k).
      intuition.
    - apply expr_to_other_trace in H. fwd. eapply if_false; intuition.
      eapply weaken.
      { eapply exec_ext with (pick_sp1 := _). 1: eapply IHexec. solve_picksps_equal. }
      simpl. intros. fwd. eexists (_ ++ _ :: _).
      repeat rewrite <- (app_assoc _ _ k2). repeat rewrite <- (app_assoc _ _ k).
      intuition.
    - econstructor; intuition. fwd. eapply weaken.
      { eapply exec_ext with (pick_sp1 := _). 1: eapply H1; eauto. solve_picksps_equal. }
      simpl. intros. fwd. eexists (_ ++ _).
      repeat rewrite <- (app_assoc _ _ k2). repeat rewrite <- (app_assoc _ _ k).
      intuition.
    - apply expr_to_other_trace in H. fwd. eapply while_false; intuition.
      eexists (_ :: _). intuition.
    - apply expr_to_other_trace in H. fwd. eapply while_true; intuition.
      { eapply exec_ext with (pick_sp1 := _). 1: eapply IHexec. solve_picksps_equal. }
      cbv beta in *. fwd. eapply weaken.
      { eapply exec_ext with (pick_sp1 := _). 1: eapply H3; eauto. solve_picksps_equal. }
      simpl. intros. fwd. eexists (_ ++ _ ++ _ :: _).
      repeat rewrite <- (app_assoc _ _ k2). repeat rewrite <- (app_assoc _ _ k).
      intuition.
    - apply call_args_to_other_trace in H0.
      fwd. econstructor; intuition eauto.
      { eapply exec_ext with (pick_sp1 := _). 1: eapply IHexec; eauto. solve_picksps_equal. }
      cbv beta in *. fwd. apply H3 in H0p2.
      fwd. exists retvs. intuition. exists l'. intuition. eexists (_ ++ _ :: _).
      repeat rewrite <- (app_assoc _ _ k2). repeat rewrite <- (app_assoc _ _ k).
      intuition.
    - apply call_args_to_other_trace in H0. fwd. econstructor; intuition eauto.
      apply H2 in H0. fwd. exists l'. intuition. eexists (_ :: _).
      intuition.
  Qed.
      
  End WithEnv.
End exec. Notation exec := exec.exec.

Module otherexec. Section WithEnv.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word byte}.
  Context {locals: map.map String.string word}.
  Context {env: map.map String.string (list String.string * list String.string * cmd)}.
  Context {ext_spec: ExtSpec}.
  Context (e: env).

  Local Notation metrics := MetricLog.

  Implicit Types post : trace -> io_trace -> mem -> locals -> metrics -> Prop. (* COQBUG(unification finds Type instead of Prop and fails to downgrade *)

  (*maybe input trace should be entire trace so far, but trace in postcondition should just be trace accumulated during execution.*)
  Inductive exec :
    (trace -> word) -> cmd -> trace -> io_trace -> mem -> locals -> metrics ->
    (trace -> io_trace -> mem -> locals -> metrics -> Prop) -> Prop :=
  | skip
    pick_sp k t m l mc post
    (_ : post k t m l mc)
    : exec pick_sp cmd.skip k t m l mc post
  | set x e
    pick_sp m l mc post
    k t v mc' k' (_ : eval_expr m l e mc nil = Some (v, mc', k'))
    (_ : post (k' ++ k) t m (map.put l x v) (addMetricInstructions 1
                                      (addMetricLoads 1 mc')))
    : exec pick_sp (cmd.set x e) k t m l mc post
  | unset x
    pick_sp k t m l mc post
    (_ : post k t m (map.remove l x) mc)
    : exec pick_sp (cmd.unset x) k t m l mc post
  | store sz ea ev
    pick_sp k t m l mc post
    a mc' k' (_ : eval_expr m l ea mc nil = Some (a, mc', k'))
    v mc'' k'' (_ : eval_expr m l ev mc' nil = Some (v, mc'', k''))
    m' (_ : store sz m a v = Some m')
    (_ : post (leak_word a :: k'' ++ k' ++ k) t m' l (addMetricInstructions 1
                                                        (addMetricLoads 1
                                                           (addMetricStores 1 mc''))))
    : exec pick_sp (cmd.store sz ea ev) k t m l mc post
  | stackalloc x n body
    pick_sp k t mSmall l mc post
    (_ : Z.modulo n (bytes_per_word width) = 0)
    (_ : forall mStack mCombined,
        let a := pick_sp nil in
        anybytes a n mStack ->
        map.split mCombined mSmall mStack ->
        exec pick_sp body k t mCombined (map.put l x a) (addMetricInstructions 1 (addMetricLoads 1 mc))
          (fun k' t' mCombined' l' mc' =>
             exists mSmall' mStack',
              anybytes a n mStack' /\
              map.split mCombined' mSmall' mStack' /\
              post k' t' mSmall' l' mc'))
    : exec pick_sp (cmd.stackalloc x n body) k t mSmall l mc post
  | if_true k t m l mc e c1 c2 post
    pick_sp v mc' k' (_ : eval_expr m l e mc nil = Some (v, mc', k'))
    (_ : word.unsigned v <> 0)
    (_ : exec (fun k => pick_sp (k ++ leak_bool true :: k')) c1 (leak_bool true :: k' ++ k) t m l (addMetricInstructions 2 (addMetricLoads 2 (addMetricJumps 1 mc'))) post)
    : exec pick_sp (cmd.cond e c1 c2) k t m l mc post
  | if_false e c1 c2
    pick_sp k t m l mc post
    v mc' k' (_ : eval_expr m l e mc nil = Some (v, mc', k'))
    (_ : word.unsigned v = 0)
    (_ : exec (fun k => pick_sp (k ++ leak_bool false :: k')) c2 (leak_bool false :: k' ++ k) t m l (addMetricInstructions 2 (addMetricLoads 2 (addMetricJumps 1 mc'))) post)
    : exec pick_sp (cmd.cond e c1 c2) k t m l mc post
  | seq c1 c2
    k t m l mc pick_sp post
    mid (_ : exec pick_sp c1 k t m l mc mid)
    (_ : forall k' t' m' l' mc',
        mid k' t' m' l' mc' ->
        exec (fun k0 => pick_sp (k0 ++ firstn (length k' - length k) k')) c2 k' t' m' l' mc' post)
    : exec pick_sp (cmd.seq c1 c2) k t m l mc post
  | while_false e c
    pick_sp k t m l mc post
    v mc' k' (_ : eval_expr m l e mc nil = Some (v, mc', k'))
    (_ : word.unsigned v = 0)
    (_ : post (leak_bool false :: k' ++ k) t m l (addMetricInstructions 1
                                                    (addMetricLoads 1
                                                       (addMetricJumps 1 mc'))))
    : exec pick_sp (cmd.while e c) k t m l mc post
  | while_true e c
      pick_sp k t m l mc post
      v mc' k' (_ : eval_expr m l e mc nil = Some (v, mc', k'))
      (_ : word.unsigned v <> 0)
      mid (_ : exec (fun k0 => pick_sp (k0 ++ leak_bool true :: k')) c (leak_bool true :: k' ++ k) t m l mc' mid)
      (_ : forall k'' t' m' l' mc'',
          mid k'' t' m' l' mc'' ->
          exec (fun k0 => pick_sp (k0 ++ firstn (length k'' - length k) k'')) (cmd.while e c) k'' t' m' l' (addMetricInstructions 2
                                                                                                              (addMetricLoads 2
                                                                                                                 (addMetricJumps 1 mc''))) post)
    : exec pick_sp (cmd.while e c) k t m l mc post
  | call binds fname arges
      pick_sp k t m l mc post
      params rets fbody (_ : map.get e fname = Some (params, rets, fbody))
      args mc' k' (_ : evaluate_call_args_log m l arges mc nil = Some (args, mc', k'))
      lf (_ : map.of_list_zip params args = Some lf)
      mid (_ : exec (fun k0 => pick_sp (k0 ++ leak_unit :: k')) fbody (leak_unit :: k' ++ k) t m lf (addMetricInstructions 100 (addMetricJumps 100 (addMetricLoads 100 (addMetricStores 100 mc')))) mid)
      (_ : forall k'' t' m' st1 mc'', mid k'' t' m' st1 mc'' ->
          exists retvs, map.getmany_of_list st1 rets = Some retvs /\
          exists l', map.putmany_of_list_zip binds retvs l = Some l' /\
          post k'' t' m' l' (addMetricInstructions 100 (addMetricJumps 100 (addMetricLoads 100 (addMetricStores 100 mc'')))))
    : exec pick_sp (cmd.call binds fname arges) k t m l mc post
  | interact binds action arges
      pick_sp k t m l mc post
      mKeep mGive (_: map.split m mKeep mGive)
      args mc' k' (_ :  evaluate_call_args_log m l arges mc nil = Some (args, mc', k'))
      mid (_ : ext_spec t mGive action args mid)
      (_ : forall mReceive resvals klist, mid mReceive resvals klist ->
          exists l', map.putmany_of_list_zip binds resvals l = Some l' /\
          forall m', map.split m' mKeep mReceive ->
          post (leak_list klist :: k' ++ k)%list (((mGive, action, args), (mReceive, resvals)) :: t) m' l'
            (addMetricInstructions 1
               (addMetricStores 1
                  (addMetricLoads 2 mc'))))
    : exec pick_sp (cmd.interact binds action arges) k t m l mc post
  .
  
  Context {word_ok: word.ok word} {mem_ok: map.ok mem} {ext_spec_ok: ext_spec.ok ext_spec}.

  Lemma weaken : forall pick_sp s k t m l mc post1,
      exec pick_sp s k t m l mc post1 ->
      forall post2: _ -> _ -> _ -> _ -> _ -> Prop,
        (forall k' t' m' l' mc', post1 k' t' m' l' mc' -> post2 k' t' m' l' mc') ->
        exec pick_sp s k t m l mc post2.
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

  Lemma intersect : forall pick_sp k t l m mc s post1,
      exec pick_sp s k t m l mc post1 ->
      forall post2,
        exec pick_sp s k t m l mc post2 ->
        exec pick_sp s k t m l mc (fun k' t' m' l' mc' => post1 k' t' m' l' mc' /\ post2 k' t' m' l' mc').
  Proof.
    induction 1;
      intros;
      match goal with
      | H: exec _ _ _ _ _ _ _ _ |- _ => inversion H; subst; clear H
      end;
      repeat match goal with
             | H1: ?e = Some (?v1, ?mc1, ?t1), H2: ?e = Some (?v2, ?mc2, ?t2) |- _ =>
               replace v2 with v1 in * by congruence;
               replace mc2 with mc1 in * by congruence;
               replace t2 with t1 in * by congruence; clear v2 mc2 t2 H2
             end;
      repeat match goal with
             | H1: ?e = Some ?v1, H2: ?e = Some ?v2 |- _ =>
               replace v2 with v1 in * by congruence; clear H2
             end;
      try solve [econstructor; eauto | exfalso; congruence].
    
    - econstructor. 1: eassumption.
      intros.
      rename H0 into Ex1, H14 into Ex2.
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
      + eapply IHexec. exact H6. (* not H *)
      + simpl. intros *. intros [? ?]. eauto.
    - eapply while_true. 1, 2: eassumption.
      + eapply IHexec. exact H10. (* not H1 *)
      + simpl. intros *. intros [? ?]. eauto.
    - eapply call. 1, 2, 3: eassumption.
      + eapply IHexec. exact H18. (* not H2 *)
      + simpl. intros *. intros [? ?].
        edestruct H3 as (? & ? & ? & ? & ?); [eassumption|].
        edestruct H19 as (? & ? & ? & ? & ?); [eassumption|].
        repeat match goal with
               | H1: ?e = Some ?v1, H2: ?e = Some ?v2 |- _ =>
                 replace v2 with v1 in * by congruence; clear H2
               end.
        eauto 10.
    - pose proof ext_spec.unique_mGive_footprint as P.
      specialize P with (1 := H1) (2 := H16).
      destruct (map.split_diff P H H7). subst mKeep0 mGive0. clear H7.
      eapply interact. 1,2: eassumption.
      + eapply ext_spec.intersect; [ exact H1 | exact H16 ].
      + simpl. intros *. intros [? ?].
        edestruct H2 as (? & ? & ?); [eassumption|].
        edestruct H17 as (? & ? & ?); [eassumption|].
        repeat match goal with
               | H1: ?e = Some ?v1, H2: ?e = Some ?v2 |- _ =>
                 replace v2 with v1 in * by congruence; clear H2
               end.
        eauto 10.
  Qed.

  Require Import coqutil.Z.Lia.

  Lemma eval_expr_extends_trace :
    forall e0 m l mc k v mc' k',
    eval_expr m l e0 mc k = Some (v, mc', k') ->
    exists k'', k' = k'' ++ k.
  Proof.
    intros e0. induction e0; intros; simpl in *;
      repeat match goal with
        | H: (let (_, _) := ?x in _) = _ |- _ =>
            destruct x
        | H: match ?x with
             | Some _ => _
             | None => _
             end = Some (_, _, _) |- _ =>
            destruct x eqn:?; try congruence
        | H: Some (?v1, ?mc1, ?t1) = Some (?v2, ?mc2, ?t2) |- _ =>
            injection H; intros; subst
        end.
    - eexists. trace_alignment.
    - eexists. trace_alignment.
    - specialize IHe0 with (1 := Heqo). fwd. eexists. trace_alignment.
    - specialize IHe0 with (1 := Heqo). fwd. eexists. trace_alignment.
    - specialize IHe0_1 with (1 := Heqo). specialize IHe0_2 with (1 := Heqo0). fwd.
      eexists. trace_alignment.
    - specialize IHe0_1 with (1 := Heqo). destruct (word.eqb _ _).
      + specialize IHe0_3 with (1 := H). fwd. eexists. trace_alignment.
      + specialize IHe0_2 with (1 := H). fwd. eexists. trace_alignment.
  Qed.

  Lemma evaluate_call_args_log_extends_trace :
    forall arges m l mc k args mc' k',
    evaluate_call_args_log m l arges mc k = Some (args, mc', k') ->
    exists k'', k' = k'' ++ k.
  Proof.
    intros arges. induction arges.
    - simpl. intros. injection H. intros. subst. eexists. trace_alignment.
    - simpl. intros. destruct (eval_expr _ _ _ _ _) eqn:E1; try congruence.
      destruct p. destruct p. destruct (evaluate_call_args_log _ _ _ _ _) eqn:E2; try congruence.
      destruct p. destruct p. injection H. intros. subst.
      apply eval_expr_extends_trace in E1. specialize IHarges with (1 := E2).
      fwd. eexists. trace_alignment.
  Qed.

  Local Ltac subst_exprs :=
    repeat match goal with
      | H : eval_expr _ _ _ _ _ = Some _ |- _ =>
          apply eval_expr_extends_trace in H; destruct H; subst
      | H : evaluate_call_args_log _ _ _ _ _ = Some _ |- _ =>
          apply evaluate_call_args_log_extends_trace in H; destruct H; subst
        end.

  Lemma exec_extends_trace pick_sp s k t m l mc post :
    exec pick_sp s k t m l mc post ->
    exec pick_sp s k t m l mc (fun k' t' m' l' mc' => post k' t' m' l' mc' /\ exists k'', k' = k'' ++ k).
  Proof.
    intros H. induction H; try (econstructor; intuition eauto; subst_exprs; eexists; trace_alignment; fail).
    - econstructor; intuition eauto. intros. eapply weaken. 1: eapply H1; eauto.
      simpl. intros. fwd. eexists. eexists. intuition eauto.
    - eapply if_true; intuition eauto. eapply weaken. 1: eapply IHexec.
      simpl. intros. fwd. intuition eauto. subst_exprs. eexists. trace_alignment.
    - eapply if_false; intuition eauto. eapply weaken. 1: eapply IHexec.
      simpl. intros. fwd. intuition eauto. subst_exprs. eexists. trace_alignment.
    - econstructor; intuition eauto. fwd. eapply weaken. 1: eapply H1; eauto.
      simpl. intros. fwd. intuition eauto. eexists. trace_alignment.
    - eapply while_true; eauto. simpl. intros. fwd. eapply weaken. 1: eapply H3; eauto.
      simpl. intros. fwd. intuition eauto. subst_exprs. eexists. trace_alignment.
    - econstructor; intuition eauto. fwd. specialize H3 with (1 := H4p0). fwd.
      eexists. intuition eauto. eexists. intuition eauto. subst_exprs.
      eexists. trace_alignment.
    - econstructor; intuition eauto. specialize H2 with (1 := H3). fwd.
      eexists. intuition eauto. subst_exprs. eexists. trace_alignment.
  Qed.

  Lemma exec_ext pick_sp1 s k t m l mc post :
    exec pick_sp1 s k t m l mc post ->
    forall pick_sp2,
    (forall k', pick_sp1 k' = pick_sp2 k') ->
    exec pick_sp2 s k t m l mc post.
  Proof.
    intros H1. induction H1; intros; try solve [econstructor; eauto].
    econstructor; eauto. intros. replace (pick_sp nil) with (pick_sp2 nil) in *.
    { subst a. eapply weaken. 1: eapply H1; eauto. simpl. eauto. }
    symmetry. apply H2 with (k' := nil).
  Qed.
  
  Local Ltac solve_picksps_equal :=
    intros; cbv beta; f_equal;
    repeat (rewrite rev_app_distr || cbn [rev app]); rewrite List.skipn_app_r;
    [|repeat (rewrite app_length || rewrite rev_length || simpl); blia];
    repeat rewrite <- app_assoc; rewrite List.skipn_app_r;
    [|rewrite rev_length; reflexivity];
    repeat (rewrite rev_app_distr || cbn [rev app] || rewrite rev_involutive);
    repeat rewrite <- app_assoc; reflexivity.

  (*Lemma exec_to_other_trace (pick_sp: PickSp) s k1 k2 t m l mc post :
    exec s k1 t m l mc post ->
    exec (pick_sp := fun k => pick_sp (rev (skipn (length k2) (rev k)) ++ k1))
      s k2 t m l mc (fun k2' t' m' l' mc' =>
                       exists k'',
                         k2' = k'' ++ k2 /\
                           post (k'' ++ k1) t' m' l' mc').
  Proof.
    intros H. generalize dependent k2. induction H; intros.
    - econstructor. exists nil. eauto.
    - apply expr_to_other_trace in H. destruct H as [k'' [H1 H2] ]. subst.
      econstructor; intuition eauto.
    - econstructor; intuition. exists nil. intuition.
    - apply expr_to_other_trace in H. apply expr_to_other_trace in H0.
      destruct H as [k''a [H3 H4] ]. subst. destruct H0 as [k''v [H5 H6] ]. subst.
      econstructor; intuition eauto. eexists (_ :: _ ++ _). simpl.
      repeat rewrite <- (app_assoc _ _ k2). repeat rewrite <- (app_assoc _ _ k).
      intuition.
    - econstructor; intuition. intros.
      replace (rev k2) with (rev k2 ++ nil) in * by apply app_nil_r. Search (length (rev _)).
      rewrite List.skipn_app_r in * by (rewrite rev_length; reflexivity).
      simpl in *. eapply weaken. 1: eapply H1; eauto.
      simpl. intros. fwd. exists mSmall', mStack'. intuition. eauto.
    - apply expr_to_other_trace in H. fwd. eapply if_true; intuition eauto.
      eapply weaken.
      { eapply exec_ext with (pick_sp1 := _). 1: eapply IHexec. solve_picksps_equal. }
      simpl. intros. fwd. eexists (_ ++ _ :: _).
      repeat rewrite <- (app_assoc _ _ k2). repeat rewrite <- (app_assoc _ _ k).
      intuition.
    - apply expr_to_other_trace in H. fwd. eapply if_false; intuition.
      eapply weaken.
      { eapply exec_ext with (pick_sp1 := _). 1: eapply IHexec. solve_picksps_equal. }
      simpl. intros. fwd. eexists (_ ++ _ :: _).
      repeat rewrite <- (app_assoc _ _ k2). repeat rewrite <- (app_assoc _ _ k).
      intuition.
    - econstructor; intuition. fwd. eapply weaken.
      { eapply exec_ext with (pick_sp1 := _). 1: eapply H1; eauto. solve_picksps_equal. }
      simpl. intros. fwd. eexists (_ ++ _).
      repeat rewrite <- (app_assoc _ _ k2). repeat rewrite <- (app_assoc _ _ k).
      intuition.
    - apply expr_to_other_trace in H. fwd. eapply while_false; intuition.
      eexists (_ :: _). intuition.
    - apply expr_to_other_trace in H. fwd. eapply while_true; intuition.
      { eapply exec_ext with (pick_sp1 := _). 1: eapply IHexec. solve_picksps_equal. }
      cbv beta in *. fwd. eapply weaken.
      { eapply exec_ext with (pick_sp1 := _). 1: eapply H3; eauto. solve_picksps_equal. }
      simpl. intros. fwd. eexists (_ ++ _ ++ _ :: _).
      repeat rewrite <- (app_assoc _ _ k2). repeat rewrite <- (app_assoc _ _ k).
      intuition.
    - apply call_args_to_other_trace in H0.
      fwd. econstructor; intuition eauto.
      { eapply exec_ext with (pick_sp1 := _). 1: eapply IHexec; eauto. solve_picksps_equal. }
      cbv beta in *. fwd. apply H3 in H0p2.
      fwd. exists retvs. intuition. exists l'. intuition. eexists (_ ++ _ :: _).
      repeat rewrite <- (app_assoc _ _ k2). repeat rewrite <- (app_assoc _ _ k).
      intuition.
    - apply call_args_to_other_trace in H0. fwd. econstructor; intuition eauto.
      apply H2 in H0. fwd. exists l'. intuition. eexists (_ :: _).
      intuition.
  Qed.*)
      
  End WithEnv.
End otherexec. Notation otherexec := otherexec.exec.

Module twoexecs. Section WithEnv.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word byte}.
  Context {locals: map.map String.string word}.
  Context {env: map.map String.string (list String.string * list String.string * cmd)}.
  Context {ext_spec: ExtSpec}.
  Context (e: env).

  Local Notation metrics := MetricLog.

  Implicit Types post : trace -> io_trace -> mem -> locals -> metrics -> Prop. (* COQBUG(unification finds Type instead of Prop and fails to downgrade *) Print eval_expr.
  Check call_args_to_other_trace.

  Ltac start_with_nil :=
    repeat match goal with
      | H: eval_expr _ _ _ _ ?k = Some (_, _, _) |- _ =>
        tryif (assert (k = nil) by reflexivity) then fail else
        (apply expr_to_other_trace in H;
        let H' := fresh "H" in
        destruct H as [? [? H']];
        subst;
        specialize (H' nil))
    end.

  Require Import Lia.

  Lemma global_to_local pick_sp s k t m l mc post :
    exec e (pick_sp := pick_sp) s k t m l mc post ->
    otherexec e (fun k' => pick_sp (k' ++ k)) s k t m l mc post.
  Proof.
    intros H. induction H; start_with_nil; try solve [econstructor; eauto; repeat rewrite app_nil_r; assumption].
    - eapply otherexec.if_true; eauto. repeat rewrite app_nil_r.
      eapply otherexec.exec_ext; try eassumption. intros. simpl.
      repeat rewrite <- app_assoc. reflexivity.
    - eapply otherexec.if_false; eauto. repeat rewrite app_nil_r.
      eapply otherexec.exec_ext; try eassumption. intros. simpl.
      repeat rewrite <- app_assoc. reflexivity.
    - econstructor.
      + eapply otherexec.exec_extends_trace. eassumption.
      + simpl. intros. fwd. rewrite app_length. (*terrible name*)
        replace (length k'' + _ - _) with (length k'') by lia.
        rewrite List.firstn_app_l by reflexivity.
        eapply otherexec.exec_ext.
        -- eapply H1; eauto.
        -- intros. simpl. repeat rewrite <- app_assoc. reflexivity.
    - eapply otherexec.while_true.
      + eassumption.
      + assumption.
      + repeat rewrite app_nil_r. eapply otherexec.exec_extends_trace.
        eapply otherexec.exec_ext; try eassumption.
        intros. simpl. repeat rewrite <- app_assoc. reflexivity.
      + simpl. intros. fwd. eapply otherexec.exec_ext.
        -- eapply H3; eauto.
        -- simpl. intros. f_equal. repeat rewrite <- app_assoc. f_equal.
           remember (k''0 ++ leak_bool true :: x) as dontcare.
           replace (k''0 ++ leak_bool true :: x ++ k) with (dontcare ++ k).
           { rewrite List.firstn_app_l; try reflexivity. rewrite app_length. lia. }
           subst. rewrite <- app_assoc. reflexivity.
    - apply call_args_to_other_trace in H0. fwd. specialize (H0p1 nil).
      econstructor; eauto. rewrite app_nil_r.
      eapply otherexec.exec_ext; try eassumption.
      simpl. intros. repeat rewrite <- app_assoc. reflexivity.
    - apply call_args_to_other_trace in H0. fwd. specialize (H0p1 nil).
      econstructor; eauto. intros. specialize (H2 _ _ _ ltac:(eassumption)).
      fwd. eexists; intuition eauto. rewrite app_nil_r. auto.
  Qed.

  Ltac from_nil :=
    repeat match goal with
      | H: eval_expr _ _ _ _ ?k = Some (_, _, _) |- _ =>
          let E := fresh in
          assert (E:k = nil) by reflexivity; clear E;
          apply expr_to_other_trace in H;
          destruct H as [? [? ?]];
          subst;
          rewrite app_nil_r in *
    end.

  Lemma local_to_global pick_sp s k t m l mc post :
    otherexec e pick_sp s k t m l mc post ->
    exec e (pick_sp := (fun k' => pick_sp (firstn (length k' - length k) k'))) s k t m l mc post.
  Proof.
    intros H. induction H; from_nil; try solve [econstructor; eauto].
    - econstructor; eauto. replace (_ - _) with 0%nat by lia. assumption.
    - eapply exec.if_true; eauto. eapply exec.exec_ext; try eassumption.
      simpl. intros. f_equal. repeat (rewrite app_length || simpl).
      replace (_ + _ - _) with (length k') by lia.
      replace (_ + _ - _) with (length k' + S (length x)) by lia.
      rewrite List.firstn_app_l; try reflexivity.
      replace (k' ++ leak_bool true :: x ++ k) with ((k' ++ leak_bool true :: x) ++ k).
      { rewrite List.firstn_app_l; try reflexivity. rewrite app_length. simpl. lia. }
      repeat (rewrite <- app_assoc || simpl). reflexivity.
    - eapply exec.if_false; eauto. eapply exec.exec_ext; try eassumption.
      simpl. intros. f_equal. repeat (rewrite app_length || simpl).
      replace (_ + _ - _) with (length k') by lia.
      replace (_ + _ - _) with (length k' + S (length x)) by lia.
      rewrite List.firstn_app_l; try reflexivity.
      replace (k' ++ leak_bool false :: x ++ k) with ((k' ++ leak_bool false :: x) ++ k).
      { rewrite List.firstn_app_l; try reflexivity. rewrite app_length. simpl. lia. }
      repeat (rewrite <- app_assoc || simpl). reflexivity.
    - econstructor.
      + eapply exec.exec_extends_trace. eassumption.
      + simpl. intros. fwd. eapply exec.exec_ext; eauto. simpl. intros. f_equal.
        repeat rewrite app_length.
        replace _ with (length k') by lia.
        replace (_ + _ - _) with (length k'') by lia.
        replace (_ + _ - _) with (length k' + length k'') by lia.
        rewrite firstn_app_2. repeat rewrite List.firstn_app_l by reflexivity. reflexivity.
    - eapply exec.while_true; [eauto | eauto | eauto | ..].
      + eapply exec.exec_extends_trace. eapply exec.exec_ext; eauto.
        simpl. intros. f_equal. repeat rewrite app_length || simpl.
        replace _ with (length k') by lia.
        replace (_ + _ - _) with (length k' + S (length x)) by lia.
        rewrite firstn_app_2. simpl.
        repeat rewrite List.firstn_app_l by reflexivity. reflexivity.
      + simpl. intros. fwd. eapply exec.exec_ext; eauto. simpl. intros. f_equal.
        repeat rewrite app_length || simpl.
        replace _ with (length k') by lia.
        replace (_ + _ - _) with (length k''0 + S (length x)) by lia.
        replace (_ + _ - _) with (length k' + (length k''0 + S (length x))) by lia.
        repeat rewrite firstn_app_2 || simpl.
        repeat rewrite List.firstn_app_l by reflexivity. reflexivity.
    - apply call_args_to_other_trace in H0. fwd. econstructor; eauto.
      rewrite app_nil_r in *. eapply exec.exec_ext; eauto. simpl. intros. f_equal.
      repeat rewrite app_length || simpl.
      replace _ with (length k') by lia.
      replace (_ + _ - _) with (length k' + S (length k'')) by lia.
      rewrite firstn_app_2. simpl.
      repeat rewrite List.firstn_app_l by reflexivity. reflexivity.
    - apply call_args_to_other_trace in H0. fwd. rewrite app_nil_r in *.
      econstructor; eauto.
  Qed.
     
  Lemma local_equiv_global s k t m l mc post :
    (forall pick_sp, otherexec e pick_sp s k t m l mc post) <->
      (forall pick_sp, exec e (pick_sp := pick_sp) s k t m l mc post).
  Proof.
    split; intros H pick_sp.
    - eapply exec.exec_ext with (pick_sp1 := _).
      + eapply local_to_global. eauto.
      + instantiate (1 := fun k' => (pick_sp (k' ++ k))). intros. simpl.
        rewrite app_length. replace (_ + _ - _) with (length k') by lia.
        rewrite List.firstn_app_l by reflexivity. reflexivity.
    - eapply otherexec.exec_ext.
      + eapply global_to_local. eauto.
      + instantiate (1 := fun k' => pick_sp (firstn (length k' - length k) k')).
        intros. simpl. rewrite app_length. replace (_ + _ - _) with (length k') by lia.
        rewrite List.firstn_app_l by reflexivity. reflexivity.
  Qed.
