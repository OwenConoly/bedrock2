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
Require Import Coq.Logic.ClassicalFacts.

Print Memory.store.

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

Lemma app_one_l {A} (a : A) ll : (a :: ll = (cons a nil) ++ ll)%list.
Proof. reflexivity. Qed.

Require Import Coq.Lists.List.
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
| leak_list : list word -> event
(* ^we need this, because sometimes it's convenient that one io call leaks only one event
   See Interact case of spilling transform_trace function for an example. *)
| consume_word : word -> event.
(*This looks pretty, but it seems hard to work with.  Can't even use the inversion tactic?
Inductive event : Type :=
| leak : forall {A : Type}, A -> event
| consume : forall {A : Type}, A -> event.*)

Inductive qevent {width: Z}{BW: Bitwidth width}{word: word.word width} : Type :=
| qleak_unit : qevent
| qleak_bool : bool -> qevent
| qleak_word : word -> qevent
| qleak_list : list word -> qevent
| qconsume_word : qevent
| qend : qevent.

Inductive abstract_trace {width: Z}{BW: Bitwidth width}{word: word.word width} : Type :=
| empty
| aleak_unit (after : abstract_trace)
| aleak_bool (b : bool) (after : abstract_trace)
| aleak_word (w : word) (after : abstract_trace)
| aleak_list (l : list word) (after : abstract_trace)
| aconsume_word (after : word -> abstract_trace).

Section WithIOEvent.
  Context {width: Z}{BW: Bitwidth width}{word: word.word width}{mem: map.map word byte}.

  (*should I call this leakage_trace, now that it doesn't contain io events?
    shame to lengthen the name. No, I shouldn't call it a leakage trace, since 
    it contains the sources of nondeterminism as well as leakage events.*)
  Definition trace : Type := list event.
  Definition io_trace : Type := list io_event.

  Definition need_to_predict e :=
    match e with
    | consume_word _ => True
    | _ => False
    end.
  
  Inductive predicts : (trace -> event) -> trace -> Prop :=
  | predicts_cons :
    forall f e k,
      (need_to_predict e -> f nil = e) ->
      predicts (fun k' => f (e :: k')) k ->
      predicts f (e :: k)
  | predicts_nil :
    forall f,
      predicts f nil.
  
  Lemma predicts_ext f k g :
    (forall k', f k' = g k') ->
    predicts f k ->
    predicts g k.
  Proof.
    intros H1 H2. revert H1. revert g. induction H2.
    - intros g0 Hfg0. econstructor.
      + rewrite <- Hfg0. apply H.
      + apply IHpredicts. intros. apply Hfg0.
    - intros. constructor.
  Qed.
  
  Lemma predict_cons f k1 k2 e :
    predicts f (k1 ++ e :: k2) ->
    need_to_predict e ->
    f k1 = e.
  Proof.
    revert k2. revert e. revert f. induction k1.
    - intros. inversion H. subst. auto.
    - intros. inversion H. subst. apply IHk1 with (1 := H5) (2 := H0).
  Qed.
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

  Definition PickSp {width: Z}{BW: Bitwidth width}{word: word.word width}{mem: map.map word byte} : Type :=
  trace -> word.
  Existing Class PickSp.

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

    Lemma eval_expr_extends_trace :
    forall e0 mc k v mc' k',
      eval_expr e0 mc k = Some (v, mc', k') ->
      exists k'', k' = k'' ++ k /\ forall x, ~In (consume_word x) k''.
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
      - eexists. split; [trace_alignment|]. auto.
      - eexists. split; [trace_alignment|]. auto.
      - specialize IHe0 with (1 := Heqo). fwd. eexists. split; [trace_alignment|].
        simpl. intros x H. destruct H; [congruence|]. rewrite app_nil_r in H.
        eapply IHe0p1. eassumption.
      - specialize IHe0 with (1 := Heqo). fwd. eexists. split; [trace_alignment|].
      simpl. intros x H. destruct H; [congruence|].  rewrite app_nil_r in H.
      (*why does eauto not work here:( *) eapply IHe0p1. eassumption.
    - specialize IHe0_1 with (1 := Heqo). specialize IHe0_2 with (1 := Heqo0). fwd.
      eexists. split; [trace_alignment|]. intros x H. rewrite app_nil_r in H.
      assert (In (consume_word x) (k'' ++ k''0)).
      + destruct op; simpl in H; try assumption.
        all: destruct H; [congruence|]; try assumption.
        all: destruct H; [congruence|]; assumption.
      + Search (In _ (_ ++ _)). apply in_app_or in H0. destruct H0.
        -- eapply IHe0_2p1. eassumption.
        -- eapply IHe0_1p1. eassumption.
    - specialize IHe0_1 with (1 := Heqo). destruct (word.eqb _ _).
      + specialize IHe0_3 with (1 := H). fwd. eexists. split; [trace_alignment|].
        intros x H'. rewrite app_nil_r in H'. apply in_app_or in H'. destruct H'.
        -- eapply IHe0_3p1. eassumption.
        -- destruct H0; [congruence|]. eapply IHe0_1p1. eassumption.
      + specialize IHe0_2 with (1 := H). fwd. eexists. split; [trace_alignment|].
        intros x H'. rewrite app_nil_r in H'. apply in_app_or in H'. destruct H'.
        -- eapply IHe0_2p1. eassumption.
        -- destruct H0; [congruence|]. eapply IHe0_1p1. eassumption.
  Qed.

  Lemma evaluate_call_args_log_extends_trace :
    forall arges mc k args mc' k',
    evaluate_call_args_log arges mc k = Some (args, mc', k') ->
    exists k'', k' = k'' ++ k /\ forall x, ~In (consume_word x) k''.
  Proof.
    intros arges. induction arges.
    - simpl. intros. injection H. intros. subst. eexists. split; [trace_alignment|]. auto.
    - simpl. intros. destruct (eval_expr  _ _ _) eqn:E1; try congruence.
      destruct p. destruct p. destruct (evaluate_call_args_log _ _ _) eqn:E2; try congruence.
      destruct p. destruct p. injection H. intros. subst.
      apply eval_expr_extends_trace in E1. specialize IHarges with (1 := E2).
      fwd. eexists. split; [trace_alignment|]. intros x H. rewrite app_nil_r in H.
      apply in_app_or in H. destruct H.
      + eapply IHargesp1. eassumption.
      + eapply E1p1. eassumption.
  Qed.
  End WithMemAndLocals.
End semantics.

Ltac subst_exprs :=
  repeat match goal with
    | H : eval_expr _ _ _ _ _ = Some _ |- _ =>
        apply eval_expr_extends_trace in H; destruct H as [? [? ?] ]; subst
    | H : evaluate_call_args_log _ _ _ _ _ = Some _ |- _ =>
        apply evaluate_call_args_log_extends_trace in H; destruct H as [? [? ?] ]; subst
    end.

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
  Inductive exec :
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
    (_ : forall a mStack mCombined,
        anybytes a n mStack ->
        map.split mCombined mSmall mStack ->
        exec body (consume_word a :: k) t mCombined (map.put l x a) (addMetricInstructions 1 (addMetricLoads 1 mc))
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

  Definition state : Type := trace * io_trace * mem * locals * metrics. Print cmd.cmd.
  Notation ami := addMetricInstructions.
  Notation aml := addMetricLoads.
  Notation ams := addMetricStores. Check locals.
  Notation amj := addMetricJumps.

  Inductive scmd :=
  | sskip
  | sset (lhs : String.string) (rhs : expr)
  | sunset (lhs : String.string)
  | sstore (_ : access_size) (address : expr) (value : expr)
  | sstackalloc (lhs : String.string) (nbytes : Z) (body : scmd)
  | start_stackalloc (lhs : String.string) (nbytes : Z) (a : word)
  | end_stackalloc (nbytes : Z) (a : word)
  (* { lhs = alloca(nbytes); body; /*allocated memory freed right here*/ } *)
  | scond (condition : expr) (nonzero_branch zero_branch : scmd)
  | sseq (s1 s2: scmd)
  | swhile (test : expr) (body : scmd)
  | jump_back
  | scall (binds : list String.string) (function : String.string) (args: list expr)
  | start_call (binds : list String.string) (params : list String.string) (rets: list String.string) (fbody: scmd) (args: list expr)
  | end_call (binds : list String.string) (rets: list String.string) (l : locals)
  | sinteract (binds : list String.string) (action : String.string) (args: list expr).
  
  Fixpoint inclusion (s : cmd) :=
    match s with
    | cmd.skip => sskip
    | cmd.set x1 x2 => sset x1 x2
    | cmd.unset x1 => sunset x1
    | cmd.store x1 x2 x3 => sstore x1 x2 x3
    | cmd.stackalloc x1 x2 x3 => sstackalloc x1 x2 (inclusion x3)
    | cmd.cond x1 x2 x3 => scond x1 (inclusion x2) (inclusion x3)
    | cmd.seq x1 x2 => sseq (inclusion x1) (inclusion x2)
    | cmd.while x1 x2 => swhile x1 (inclusion x2)
    | cmd.call x1 x2 x3 => scall x1 x2 x3
    | cmd.interact x1 x2 x3 => sinteract x1 x2 x3
    end.

  Inductive step :
    scmd -> trace -> io_trace -> mem -> locals -> metrics ->
    scmd -> trace -> io_trace -> mem -> locals -> metrics -> Prop :=
  | set_step x e
      m l mc
      k t v mc' k' (_ : eval_expr m l e mc k = Some (v, mc', k'))
    : step (sset x e) k t m l mc
        sskip k' t m (map.put l x v) (ami 1 (aml 1 mc'))
  | unset_step x
    k t m l mc
    : step (sunset x) k t m l mc
        sskip k t m (map.remove l x) mc
  | store_step sz ea ev
    k t m l mc
    a mc' k' (_ : eval_expr m l ea mc k = Some (a, mc', k'))
    v mc'' k'' (_ : eval_expr m l ev mc' k' = Some (v, mc'', k''))
    m' (_ : Memory.store sz m a v = Some m')
    : step (sstore sz ea ev) k t m l mc
        sskip (leak_word a :: k'') t m' l (ami 1 (aml 1 (ams 1 mc'')))
  | stackalloc_step x n body a
      k t m l mc
    : step (sstackalloc x n body) k t m l mc
        (sseq (start_stackalloc x n a) (sseq body (end_stackalloc n a))) k t m l mc
  | stackalloc_start_step x n a
      k t mSmall l mc
      mStack mCombined
      (_ : Z.modulo n (bytes_per_word width) = 0)
      (_ : anybytes a n mStack)
      (_ : map.split mCombined mSmall mStack)
    : step (start_stackalloc x n a) k t mSmall l mc
        sskip (consume_word a :: k) t mCombined (map.put l x a) (ami 1 (aml 1 mc))
  | stackalloc_end_step n a
      k t mCombined l mc
      mSmall mStack
      (_ : anybytes a n mStack)
      (_ : map.split mCombined mSmall mStack)
    : step (end_stackalloc n a) k t mCombined l mc
        sskip k t mSmall l mc
  | if_true_step k t m l mc e c1 c2 post
    v mc' k' (_ : eval_expr m l e mc k = Some (v, mc', k'))
    (_ : word.unsigned v <> 0)
    : step (scond e c1 c2) k t m l mc
        c1 (leak_bool true :: k') t m l (ami 2 (aml 2 (amj 1 mc')))
  | if_false_step k t m l mc e c1 c2 post
    v mc' k' (_ : eval_expr m l e mc k = Some (v, mc', k'))
    (_ : word.unsigned v = 0)
    : step (scond e c1 c2) k t m l mc
        c2 (leak_bool false :: k') t m l (ami 2 (aml 2 (amj 1 mc')))
  | seq_step c1 c2
      k t m l mc
      c1' k' t' m' l' mc'
    (_ : step c1 k t m l mc c1' k' t' m' l' mc')
    : step (sseq c1 c2) k t m l mc
        (sseq c1' c2) k' t' m' l' mc'
  | seq_done_step c2
      k t m l mc
    : step (sseq sskip c2) k t m l mc
        c2 k t m l mc
  | while_false_step e c
      k t m l mc
      v mc' k' (_ : eval_expr m l e mc k = Some (v, mc', k'))
      (_ : word.unsigned v = 0)
    : step (swhile e c) k t m l mc
        sskip (leak_bool false :: k') t m l (ami 1 (aml 1 (amj 1 mc')))
  | while_true_step e c
      k t m l mc post
      v mc' k' (_ : eval_expr m l e mc k = Some (v, mc', k'))
      (_ : word.unsigned v <> 0)
    : step (swhile e c) k t m l mc
        (sseq c (sseq jump_back (swhile e c))) (leak_bool true :: k') t m l mc'
  | jump_back_step
      k t m l mc
    : step jump_back k t m l mc
        sskip k t m l (ami 2 (aml 2 (amj 1 mc)))
  | call_step binds fname arges
      k t m l mc
      params rets fbody (_ : map.get e fname = Some (params, rets, fbody))
    : step (scall binds fname arges) k t m l mc
        (sseq (start_call binds params rets (inclusion fbody) arges) (end_call binds rets l)) k t m l mc
  | start_call_step binds params rets sfbody arges
      k t m l mc
      args mc' k' (_ : evaluate_call_args_log m l arges mc k = Some (args, mc', k'))
      lf (_ : map.of_list_zip params args = Some lf)
    : step (start_call binds params rets sfbody arges) k t m l mc
        sfbody (leak_unit :: k') t m lf (ami 100 (amj 100 (aml 100 (ams 100 mc'))))
  | end_call_step binds rets (l : locals)
      k t m (st1 : locals) mc l'
      (_ : exists retvs,
          map.getmany_of_list st1 rets = Some retvs /\
            map.putmany_of_list_zip binds retvs l = Some l')
    : step (end_call binds rets l) k t m st1 mc
        sskip k t m l' (ami 100 (amj 100 (aml 100 (ams 100 mc))))
  | interact_step binds action arges
      k t m l mc
      mKeep mGive (_: map.split m mKeep mGive)
      args mc' k' (_ : evaluate_call_args_log m l arges mc k = Some (args, mc', k'))
      (_: forall (*t0 don't need this.*) mGive0 mid0, ext_spec t mGive0 action args mid0 -> map.same_domain mGive0 mGive)
      mReceive resvals klist
      (_ : forall mid, ext_spec t mGive action args mid -> mid mReceive resvals klist)
      l' (_ : map.putmany_of_list_zip binds resvals l = Some l')
      m' (_ : map.split m' mKeep mReceive)
    : step (sinteract binds action arges) k t m l mc
        sskip (leak_list klist :: k')%list (((mGive, action, args), (mReceive, resvals)) :: t) m' l' (ami 1 (ams 1 (aml 2 mc'))).

  Definition sstate : Type := scmd * trace * io_trace * mem * locals * metrics.
  Definition get_scmd (st : sstate) : scmd :=
    let '(s, k, t, m, l, mc) := st in s.

  Definition other_inclusion st : sstate :=
    let '(s, k, t, m, l, mc) := st in
    (inclusion s, k, t, m, l, mc).

  Definition state_step st1 st2 :=
    let '(s1, k1, t1, m1, l1, mc1) := st1 in
    let '(s2, k2, t2, m2, l2, mc2) := st2 in
    step s1 k1 t1 m1 l1 mc1 s2 k2 t2 m2 l2 mc2.

  Definition done_state f i :=
    get_scmd (f i) = sskip /\ f (S i) = f i.

  Definition stuck_state f i :=
    (~exists st, state_step (f i) st) /\ f (S i) = f i.

  Definition step_state f i :=
    state_step (f i) (f (S i)).

  Definition possible_execution (f : nat -> sstate) :=
    forall i, step_state f i \/ stuck_state f i.

  Inductive nondet_stuck : sstate -> Prop :=
  | nondet_stuck_stackalloc : forall k t m l mc x n a,
      Z.modulo n (bytes_per_word width) = 0 ->
      (~exists st, state_step (start_stackalloc x n a, k, t, m, l, mc) st) ->
      nondet_stuck (start_stackalloc x n a, k, t, m, l, mc)
  | nondet_stuck_interact : forall k t m l mc binds action arges mKeep mGive args mc' k',
      map.split m mKeep mGive ->
      evaluate_call_args_log m l arges mc k = Some (args, mc', k') ->
      (forall mGive0 mid0, ext_spec t mGive0 action args mid0 -> map.same_domain mGive0 mGive) ->
      (~exists st, state_step (sinteract binds action arges, k, t, m, l, mc) st) ->
      nondet_stuck (sinteract binds action arges, k, t, m, l, mc)
  | nondet_stuck_seq : forall s1 s2 k t m l mc,
    nondet_stuck (s1, k, t, m, l, mc) ->
    nondet_stuck (sseq s1 s2, k, t, m, l, mc).

  Definition state_satisfies st post : Prop :=
    (let '(s, k, t, m, l, mc) := st in s = sskip /\ post k t m l mc) \/
      nondet_stuck st.

  Definition satisfies (f : nat -> _) post := exists i, state_satisfies (f i) post.

  Definition comes_right_after s1 s2 :=
    state_step s2 s1.
  Definition lifted_comes_right_after s1 s2 :=
    comes_right_after (other_inclusion s1) (other_inclusion s2).
  Print state.
  Inductive prefix : sstate -> sstate -> Prop :=
  | bprefix : forall s1 s2 k t m l mc,
      prefix (s1, k, t, m, l, mc) (sseq s1 s2, k, t, m, l, mc).

  Definition comes_right_after_or_prefix s1 s2 :=
    comes_right_after s1 s2 \/ prefix s1 s2.

  Definition lifted_comes_right_after_or_prefix s1 s2 :=
    comes_right_after_or_prefix (other_inclusion s1) (other_inclusion s2).

  Definition comes_after := clos_trans _ comes_right_after.
  Definition lifted_comes_after s1 s2 := comes_after (other_inclusion s1) (other_inclusion s2).

  Definition comes_after_or_prefix := clos_trans _ comes_right_after_or_prefix.
  Definition lifted_comes_after_or_prefix s1 s2 := comes_after_or_prefix (other_inclusion s1) (other_inclusion s2).

  Definition first_part st : sstate :=
    match st with
    | (sseq s1 s2, k, t, m, l, mc) => (s1, k, t, m, l, mc)
    | _ => (sskip, nil, nil, map.empty, map.empty, EmptyMetricLog)
    end.
  
  Fixpoint execution_of_first_part (f : nat -> sstate) n :=
    match n with
    | O => first_part (f O)
    | S n' =>
        match (execution_of_first_part f n') with
        | (sskip, _, _, _, _, _) => execution_of_first_part f n'
        | _ => first_part (f n)
        end
    end.

  Ltac destr_sstate st :=
    (*this is not exactly what I want, I want all of them to be named the same way...*)
    let s := fresh "s" in
    let k := fresh "k" in
    let t := fresh "t" in
    let m := fresh "m" in
    let l := fresh "l" in
    let mc := fresh "mc" in
    let Ef := fresh "Ef" in
    destruct st as [ [ [ [ [s k] t] m] l] mc] eqn:Ef.

  Lemma sskip_or_first_part' f n :
    match (execution_of_first_part f n) with
    | (sskip, _, _, _, _, _) => True
    | _ => first_part (f n) = execution_of_first_part f n
    end.
  Proof.
    destruct n.
    - simpl. destr_sstate (f 0%nat). destruct s; try reflexivity.
      destruct s1; eexists; reflexivity.
    - simpl. destr_sstate (execution_of_first_part f n). destruct s; try reflexivity.
      all: destr_sstate (first_part (f (S n))); destruct s; try reflexivity.
      all: destruct s0; reflexivity.
  Qed.

  Lemma sskip_or_first_part f n :
    (exists k t m l mc, execution_of_first_part f n = (sskip, k, t, m, l, mc)) \/
      first_part (f n) = execution_of_first_part f n.
  Proof.
    assert (H := sskip_or_first_part' f n). destr_sstate (execution_of_first_part f n).
    destruct s; try (right; assumption). left. do 5 eexists. reflexivity.
  Qed.
  
  Lemma possible_first_part f :
    possible_execution f ->
    possible_execution (execution_of_first_part f).
  Proof.
    cbv [possible_execution]. intros H n.
    specialize (H n). assert (H1 := sskip_or_first_part f n).
    destruct H1 as [H1 | H1].
    - fwd. right. cbv [stuck_state]. split.
      + intros [st H']. rewrite H1 in H'. cbv [state_step step_state] in H'.
        destr_sstate st. inversion H'.
      + simpl. rewrite H1. reflexivity.
    - destruct H as [H | H].
      + cbv [step_state state_step] in H. destr_sstate (f n).
        destr_sstate (execution_of_first_part f n).
        assert (s0 = sskip \/ exists s1 s2, s = sseq s1 s2).
        { destruct s; destruct s0; simpl in H1; try congruence.
          all: try (left; reflexivity). all: try (right; eexists; eexists; reflexivity). }
        destruct H0 as [H0 | H0].
        -- subst. right. cbv [stuck_state]. split.
           ++ intros [st H']. rewrite Ef0 in H'. cbv [state_step step_state] in H'.
              destr_sstate st. inversion H'.
           ++ simpl. rewrite Ef0. reflexivity.
        -- destruct H0 as [s1 [s2 H0] ]. subst. simpl in H1. inversion H1. subst.
           destr_sstate (f (S n)). destruct s0.
           { right. cbv [stuck_state]. inversion H; subst.
             - inversion H14.
             - split.
               + intros [st H']. destr_sstate st. cbv [state_step step_state] in H'.
                 rewrite Ef0 in H'. inversion H'.
               + simpl. rewrite Ef0. reflexivity. }
           all: left; inversion H; subst; cbv [step_state state_step]; simpl; rewrite Ef0;
             rewrite Ef1; simpl; assumption.
      + right. destruct H as [Hp1 Hp2]. split.
        -- intros [st H']. apply Hp1. clear Hp1 Hp2. rewrite <- H1 in H'. clear H1.
           cbv [state_step step_state] in *. destr_sstate (f n).           
           destr_sstate st. destruct s; simpl in H'; try solve [inversion H'].
           eexists (_, _, _, _, _, _). econstructor. eassumption.
        -- simpl. rewrite <- H1. rewrite Hp2. destr_sstate (first_part (f n)).
           destruct s; reflexivity.
  Qed.

  Require Import Lia.

  Lemma nats_have_mins n (P : _ -> Prop) :
    (forall i, P i \/ ~P i) ->
    P n ->
    exists m,
      P m /\ forall i, i < m -> ~P i.
  Proof.
    revert P. induction n.
    - intros. exists O. split; [assumption|]. intros. lia.
    - intros. specialize (IHn (fun i => P (S i))). simpl in IHn.
      specialize (IHn (fun i => H (S i))). specialize (IHn H0). fwd.
      clear H0 n. destruct (H O).
      + exists O. split; [assumption|]. lia.
      + exists (S m). split; [assumption|]. intros. destruct i.
        -- assumption.
        -- apply IHnp1. lia.
  Qed.

  Lemma possible_execution_offset f k :
    possible_execution f ->
    possible_execution (fun i => f (k + i)).
  Proof.
    cbv [possible_execution step_state stuck_state]. intros. specialize (H (k + i)).
    replace (k + S i) with (S (k + i)) by lia. assumption.
  Qed.

  Lemma satisfies_offset f k post :
    satisfies (fun i => f (k + i)) post ->
    satisfies f post.
  Proof.
    intros [i H]. cbv [satisfies]. exists (k + i). assumption.
  Qed.

  Lemma satisfies_weaken f post1 post2 :
    (forall k t m l mc, post1 k t m l mc -> post2 k t m l mc) ->
    satisfies f post1 ->
    satisfies f post2.
  Proof.
    intros H1 [i H2]. cbv [satisfies]. exists i. destruct H2.
    - destr_sstate (f i). left. intuition.
    - right. assumption.
  Qed.

  Lemma execution_of_first_part_stable' f n :
    get_scmd (execution_of_first_part f n) = sskip ->
    forall m, n <= m ->
              execution_of_first_part f n = execution_of_first_part f m.
  Proof.
    intros. replace m with ((m - n) + n) by lia. clear H0.
    induction (m - n).
    - reflexivity.
    - simpl. rewrite <- IHn0. clear IHn0.
      destr_sstate (execution_of_first_part f n). simpl in H. subst.
      reflexivity.
  Qed.

  Lemma execution_of_first_part_stable f n1 n2 :
    get_scmd (execution_of_first_part f n1) = sskip ->
    get_scmd (execution_of_first_part f n2) = sskip ->
    execution_of_first_part f n1 = execution_of_first_part f n2.
  Proof.
    intros H1 H2. assert (H3 := execution_of_first_part_stable' _ _ H1).
    assert (H4 := execution_of_first_part_stable' _ _ H2).
    Search (_ <= _ \/ _ <= _). assert (H := PeanoNat.Nat.le_ge_cases n1 n2).
    destruct H as [H | H].
    - apply H3. assumption.
    - symmetry. apply H4. assumption.
  Qed.

  Lemma first_part_1 f i :
    get_scmd (execution_of_first_part f i) <> sskip ->
    execution_of_first_part f i = first_part (f i).
  Proof.
    intros H. destruct i.
    - reflexivity.
    - simpl in *. destr_sstate (execution_of_first_part f i).
      destruct s; try reflexivity. simpl in H. congruence.
  Qed.

  Lemma second_comes_after_first s1 s2 k t m l mc k' t' m' l' mc' f i :
    f O = (sseq s1 s2, k, t, m, l, mc) ->
    possible_execution f ->
    execution_of_first_part f i = (sskip, k', t', m', l', mc') ->
    exists j,
      f j = (s2, k', t', m', l', mc').
  Proof.
    intros H1 H2 H3. assert (H4: get_scmd (execution_of_first_part f i) = sskip).
    { rewrite H3. reflexivity. }
    apply (nats_have_mins i) in H4.
    2: { intros x. destr_sstate (execution_of_first_part f x). simpl.
         destruct s; (left; reflexivity) || (right; congruence). }
    destruct H4 as [n' [H4 H5] ].
    assert (forall n, n < n' -> exists s, get_scmd (f n) = sseq s s2). (*this deserves to be its own lemma*)
    { intros n. induction n.
      - intros. simpl. rewrite H1. simpl. eexists. reflexivity.
      - intros H. specialize (IHn ltac:(lia)). fwd. specialize (H5 n ltac:(lia)).
        simpl in H5. assert (get_scmd (first_part (f n)) <> sskip).
        { intros H'. cbv [execution_of_first_part] in H5.
          destruct n.
          - apply H5. apply H'.
          - fold execution_of_first_part in H5. destr_sstate (execution_of_first_part f n).
            destr_sstate (first_part (f (S n))). simpl in H'. subst.
            destruct s0; simpl in H5; congruence. }
        destr_sstate (first_part (f n)). simpl in H0.
        assert (Hn := H2 n). destr_sstate (f n). simpl in IHn. subst.
        simpl in Ef. inversion Ef. subst. clear Ef. destruct Hn as [Hn | Hn].
        + cbv [step_state state_step] in Hn. rewrite Ef0 in Hn.
          destr_sstate (f (S n)). inversion Hn; subst.
          -- eexists. reflexivity.
          -- exfalso. apply H0. reflexivity.
        + destruct Hn as [_ Hn]. rewrite Hn. rewrite Ef0. eexists. reflexivity. }
    assert (H3': get_scmd (execution_of_first_part f i) = sskip).
    { rewrite H3. reflexivity. }
    assert (H6 := execution_of_first_part_stable _ _ _ H4 H3').
    rewrite <- H6 in *. clear H6. clear i. clear H3' H4.
    exists (S n').
    destruct n'.
    - simpl in H3. rewrite H1 in H3. simpl in H3. inversion H3. subst.
      specialize (H2 O). destruct H2 as [H2 | H2].
      + cbv [step_state state_step] in H2. rewrite H1 in H2. destr_sstate (f 1%nat).
        inversion H2; subst.
        -- inversion H17.
        -- reflexivity.
      + cbv [stuck_state] in H2. destruct H2 as [H2p1 H2p2]. exfalso. apply H2p1.
        eexists (_, _, _, _, _, _). rewrite H1. Print step. eapply seq_done_step.
    - specialize (H n' ltac:(lia)). destruct H as [s H].
      specialize (H5 n' ltac:(lia)).
      replace (execution_of_first_part f (S n')) with (first_part (f (S n'))) in *.
      2: { simpl. destr_sstate (execution_of_first_part f n'). destruct s0; try reflexivity.
           simpl in H5. congruence. }
      assert (s <> sskip).
      { intros H'. subst. destr_sstate (f n'). simpl in H. subst.
        destruct n'.
        - simpl in H5. rewrite Ef in H5. simpl in H5. apply H5. reflexivity.
        - simpl in H5. rewrite Ef in H5. destr_sstate (execution_of_first_part f n').
          destruct s; simpl in H5; congruence. }
      destr_sstate (f n'). simpl in H. subst. assert (Hn' := H2 n').
      destruct Hn' as [Hn' | Hn'].
      + cbv [step_state state_step] in Hn'. rewrite Ef in Hn'. destr_sstate (f (S n')).
        inversion Hn'; subst.
        -- simpl in H3. inversion H3. subst. clear H3. assert (HSn' := H2 (S n')).
           destruct HSn' as [HSn' | HSn'].
           ++ cbv [step_state state_step] in HSn'. rewrite Ef0 in HSn'.
              destr_sstate (f (S (S n'))). inversion HSn'; subst.
              --- inversion H16.
              --- reflexivity.
           ++ destruct HSn' as [HSn'p1 HSn'p2]. exfalso. apply HSn'p1. eexists (_, _, _, _, _, _).
              rewrite Ef0. eapply seq_done_step.
        -- congruence.
      + destruct Hn' as [Hn'p1 Hn'p2]. rewrite Ef in Hn'p2. rewrite Hn'p2 in H3. simpl in H3.
        inversion H3. subst. congruence.
  Qed.
  
  Lemma build_seq s1 s2 k t m l mc post :
    (forall (f : nat -> _),
        f O = (s1, k, t, m, l, mc) ->
        possible_execution f ->
        satisfies f (fun k' t' m' l' mc' =>
                       forall (g : nat -> _),
                         g O = (s2, k', t', m', l', mc') ->
                         possible_execution g ->
                         satisfies g post)) ->
    forall (f : nat -> _),
      f O = (sseq s1 s2, k, t, m, l, mc) ->
      possible_execution f ->
      satisfies f post.
  Proof.
    intros. specialize (H (execution_of_first_part f)).
    simpl in H. rewrite H0 in H. specialize (H eq_refl (possible_first_part _ H1)).
    destruct H as [i H]. destruct H as [H | H].
    - destr_sstate (execution_of_first_part f i). destruct H. subst.
      assert (H3 := second_comes_after_first).
      specialize H3 with (1 := H0) (2 := H1) (3 := Ef).
      destruct H3 as [j H3]. specialize (H2 (fun i => f (j + i))).
      simpl in H2. replace (j + 0) with j in H2 by lia.
      specialize (H2 H3 (possible_execution_offset _ _ H1)).
      eapply satisfies_offset. eapply H2.
    - rewrite first_part_1 in H.
      + remember (first_part (f i)) as st eqn:E. cbv [satisfies]. exists i.
        cbv [state_satisfies]. right. destr_sstate (f i). destruct H.
        -- destruct s; simpl in E; try congruence.
           inversion E. subst. clear E. constructor. constructor.
           ++ assumption.
           ++ assumption.
        -- destruct s; simpl in E; try congruence.
           inversion E. subst. clear E. constructor. econstructor; eassumption.
        -- destruct s; simpl in E; try congruence.
           inversion E. subst. clear E. constructor. constructor. assumption.
      + destr_sstate (execution_of_first_part f i). destruct s; simpl; try congruence.
        inversion H.
  Qed.
    
  Lemma invert_seq s1 s2 k t m l mc post :
    (forall (f : nat -> _),
        f O = (sseq s1 s2, k, t, m, l, mc) ->
        possible_execution f ->
        satisfies f post) ->
    (forall (f : nat -> _),
        f O = (s1, k, t, m, l, mc) ->
        possible_execution f ->
        satisfies f (fun k' t' m' l' mc' =>
                       comes_after (sskip, k', t', m', l', mc') (s1, k, t, m, l, mc) /\
                         forall (g : nat -> _),
                           g O = (s2, k', t', m', l', mc') ->
                           possible_execution g ->
                           satisfies g post)).
  Proof. Admitted.

  Ltac unify_eval_exprs :=
    repeat match goal with
      | H1: ?e = Some (?v1, ?mc1, ?t1), H2: ?e = Some (?v2, ?mc2, ?t2) |- _ =>
          replace v2 with v1 in * by congruence;
          replace mc2 with mc1 in * by congruence;
          replace t2 with t1 in * by congruence; clear v2 mc2 t2 H2
      end;
    repeat match goal with
      | H1: ?e = Some ?v1, H2: ?e = Some ?v2 |- _ =>
          replace v2 with v1 in * by congruence; clear H2
      end.

  Context {word_ok: word.ok word} {mem_ok: map.ok mem} {ext_spec_ok: ext_spec.ok ext_spec}.

  Lemma exec_to_step (s : cmd) k t m l mc post :
    excluded_middle ->
    exec s k t m l mc post ->
    forall (f : nat -> _),
      f O = (inclusion s, k, t, m, l, mc) ->
      possible_execution f ->
      satisfies f post.
  Proof.
    intros em H. induction H.
    - intros. exists O. left. rewrite H0. eauto.
    - intros f HO HS. assert (HSO := HS O). destruct HSO as [HSO | HSO ].
      + exists (S O). cbv [step_state state_step] in HSO.
        destr_sstate (f (S O)). rewrite HO in HSO.
        inversion HSO. subst. unify_eval_exprs. left. eauto.
      + exfalso. apply HSO. eexists (_, _, _, _, _, _). rewrite HO. cbv [state_step].
        econstructor; eassumption.
    - intros f HO HS. assert (HSO := HS O). destruct HSO as [HSO | HSO ].
      + exists (S O). cbv [step_state state_step] in HSO.
        destr_sstate (f (S O)). rewrite HO in HSO.
        inversion HSO. subst. unify_eval_exprs. left. eauto.
      + exfalso. apply HSO. eexists (_, _, _, _, _, _). rewrite HO. cbv [state_step].
        econstructor; eassumption.
    - intros f HO HS. assert (HSO := HS O). destruct HSO as [HSO | HSO ].
      + exists (S O). cbv [step_state state_step] in HSO.
        destr_sstate (f (S O)). rewrite HO in HSO.
        inversion HSO. subst. unify_eval_exprs. left. eauto.
      + exfalso. apply HSO. eexists (_, _, _, _, _, _). rewrite HO. cbv [state_step].
        econstructor; eassumption.
    - intros f HO HS. simpl in HO. clear H0. assert (HSO := HS O).
      destruct HSO as [HSO | HSO ].
      + cbv [step_state state_step] in HSO. rewrite HO in HSO.
        destr_sstate (f (S O)). inversion HSO. subst. clear HO. assert (HSSO := HS (S O)).
        destruct HSSO as [HSSO | HSSO ].
        * cbv [step_state state_step] in HSSO.
          simpl in HSO. rewrite Ef in HSSO. destr_sstate (f (S (S O))).
          inversion HSSO. subst. clear Ef HSO. inversion H14. subst. clear HSSO H14.
          assert (HSSSO := HS (S (S O))). destruct HSSSO as [HSSSO | HSSSO ].
          -- cbv [step_state state_step] in HSSSO. rewrite Ef0 in HSSSO.
             destr_sstate (f (S (S (S O)))). inversion HSSSO.
             ++ subst. inversion H15.
             ++ subst. clear HSSSO Ef0. eapply satisfies_offset; eauto.
                instantiate (1 := 3%nat). 
                eapply build_seq.
                2: apply Ef.
                2: apply possible_execution_offset; assumption.
                intros.
                eapply satisfies_weaken. 2: eapply H1; eauto.
                simpl. intros.
                specialize (H6 O). cbv [step_state stuck_state state_step] in H6.
                rewrite H5 in *. clear H5. destr_sstate (g (S O)).
                repeat match goal with
                       | H: anybytes _ _ _ |- _ => clear H
                       | H: map.split _ _ _ |- _ => clear H
                       end.
                destruct H6 as [H6 | H6].
                +++ inversion H6. subst. fwd.
                    match goal with
                    | A: map.split _ _ _, B: map.split _ _ _ |- _ =>
                        specialize @map.split_diff with (4 := A) (5 := B) as P
                    end.
                    edestruct P; try typeclasses eauto.
                    1: eapply anybytes_unique_domain; eassumption.
                    subst. eexists (S O). left. rewrite Ef0. auto.
                +++ exfalso. apply H6. clear H6. fwd. eexists (_, _, _, _, _, _).
                    econstructor; eauto.
          -- cbv [stuck_state] in HSSSO. exfalso. apply HSSSO. clear HSSSO.
             eexists (_, _, _, _, _, _). rewrite Ef0. cbv [state_step].
             apply seq_done_step.
        * cbv [stuck_state] in HSSO. exists (S O).
          right. rewrite Ef. constructor. constructor; eauto. intros H'.
          apply HSSO. clear HSSO. cbv [state_step] in H'. fwd. eexists (_, _, _, _, _, _).
          rewrite Ef. cbv [state_step]. constructor. eassumption.
      + exfalso. apply HSO. eexists (_, _, _, _, _, _). rewrite HO. econstructor.
    - intros f HO HS. assert (HSO := HS O). destruct HSO as [HSO | HSO].
      + cbv [step_state state_step] in HSO. rewrite HO in HSO.
        destr_sstate (f 1%nat). inversion HSO; try congruence. subst. unify_eval_exprs.
        specialize (IHexec (fun i => f (1 + i))). simpl in IHexec. rewrite Ef in IHexec.
        specialize (IHexec eq_refl). assert (Hposs := possible_execution_offset _ 1%nat HS).
        specialize (IHexec Hposs). clear Hposs. Search satisfies.
        apply (satisfies_offset _ 1%nat) in IHexec; eauto.
      + cbv [stuck_state] in HSO. exfalso. apply HSO. clear HSO. eexists (_, _, _, _, _, _).
        rewrite HO. eapply if_true_step; eauto.
    - intros f HO HS. assert (HSO := HS O). destruct HSO as [HSO | HSO].
      + cbv [step_state state_step] in HSO. rewrite HO in HSO.
        destr_sstate (f 1%nat). inversion HSO; try congruence. subst. unify_eval_exprs.
        specialize (IHexec (fun i => f (1 + i))). simpl in IHexec. rewrite Ef in IHexec.
        specialize (IHexec eq_refl). assert (Hposs := possible_execution_offset _ 1%nat HS).
        specialize (IHexec Hposs). clear Hposs. Search satisfies.
        apply (satisfies_offset _ 1%nat) in IHexec; eauto.
      + cbv [stuck_state] in HSO. exfalso. apply HSO. clear HSO. eexists (_, _, _, _, _, _).
        rewrite HO. eapply if_false_step; eauto.
    - eapply build_seq. fold inclusion. intros f H2 H3. eapply satisfies_weaken; eauto.
    - intros f HO HS. assert (HSO := HS O). destruct HSO as [HSO | HSO].
      + cbv [step_state state_step] in HSO. rewrite HO in HSO. destr_sstate (f 1%nat).
        inversion HSO; try congruence. subst. unify_eval_exprs. exists (S O). left.
        rewrite Ef. eauto.
      + exfalso. cbv [stuck_state] in HSO. apply HSO. clear HSO. eexists (_, _, _, _, _, _).
        rewrite HO. econstructor; eauto.
    - intros f HO HS. assert (HSO := HS O). destruct HSO as [HSO | HSO].
      + cbv [step_state state_step] in HSO. rewrite HO in HSO. destr_sstate (f 1%nat).
        inversion HSO; try congruence. subst. unify_eval_exprs. eapply satisfies_offset; eauto.
        instantiate (1 := 1%nat). eapply build_seq; eauto.
        2: eapply possible_execution_offset; eauto.
        intros. eapply satisfies_weaken; eauto. intros * g ? HgO HgS.
        assert (HgSO := HgS O). destruct HgSO as [HgSO | HgSO].
        -- cbv [step_state state_step] in HgSO. rewrite HgO in HgSO. destr_sstate (g0 1%nat).
           inversion HgSO. subst. inversion H20. subst. assert (HgSSO := HgS (S O)).
           destruct HgSSO as [HgSSO | HgSSO].
           ++ cbv [step_state state_step] in HgSSO. rewrite Ef0 in HgSSO.
              destr_sstate (g0 2%nat). inversion HgSSO; subst.
              --- inversion H21.
              --- eapply satisfies_offset; eauto. instantiate (1 := 2%nat).
                  eapply H3; eauto. apply possible_execution_offset. assumption.
           ++ exfalso. apply HgSSO. eexists (_, _, _, _, _, _). rewrite Ef0.
              eapply seq_done_step.
        -- exfalso. apply HgSO. eexists (_, _, _, _, _, _). rewrite HgO. econstructor.
           econstructor.
      + exfalso. apply HSO. eexists (_, _, _, _, _, _). rewrite HO. eapply while_true_step; eauto.
    - intros f HO HS. assert (HSO := HS O). destruct HSO as [HSO | HSO].
      + cbv [step_state state_step] in HSO. rewrite HO in HSO. destr_sstate (f 1%nat).
        inversion HSO. subst. unify_eval_exprs. eapply satisfies_offset.
        instantiate (1 := 1%nat). eapply build_seq; eauto.
        2: eapply possible_execution_offset; eauto.
        intros g HgO HgS. eapply satisfies_weaken.
        2: { assert (HgSO := HgS O). destruct HgSO as [HgSO | HgSO].
             - cbv [step_state state_step] in HgSO. rewrite HgO in HgSO. destr_sstate (g 1%nat).
               inversion HgSO. subst. unify_eval_exprs. eapply satisfies_offset with (k := 1%nat).
               eapply IHexec; eauto. apply possible_execution_offset; auto.
             - exfalso. apply HgSO. eexists (_, _, _, _, _, _). rewrite HgO. econstructor; eauto. }
        intros * Hmid h HhO HhS. apply H3 in Hmid. fwd.
        assert (HhSO := HhS O). destruct HhSO as [HhSO | HhSO].
        -- cbv [step_state state_step] in HhSO. rewrite HhO in HhSO. destr_sstate (h 1%nat).
           inversion HhSO. subst. fwd. unify_eval_exprs. exists (S O). left. rewrite Ef0. eauto.
        -- exfalso. apply HhSO. eexists (_, _, _, _, _, _). rewrite HhO. econstructor; eauto.
      + exfalso. apply HSO. eexists (_, _, _, _, _, _). rewrite HO. econstructor; eauto.
    - intros f HO HS. assert (HSO := HS O). destruct HSO as [HSO | HSO].
      + cbv [step_state state_step] in HSO. rewrite HO in HSO. destr_sstate (f 1%nat).
        inversion HSO. subst. unify_eval_exprs. specialize (H8 _ _ H1).
        Check map.split_diff.
        destruct (map.split_diff H8 H H6). subst. clear H6 H8.
        specialize (H9 _ H1). apply H2 in H9. fwd. apply H9p1 in H22. clear H9p1.
        unify_eval_exprs. exists (S O). rewrite Ef. left. auto.
      + assert (step_or_not :=
                  em (exists mReceive resvals klist,
                        (exists m', map.split m' mKeep mReceive)(*map.disjoint mKeep mReceive*) /\
                          forall mid',
                            ext_spec t mGive action args mid' ->
                            mid' mReceive resvals klist)).
        destruct step_or_not as [step | not_step].
        -- fwd. assert (Hmid := stepp1 _ H1). apply H2 in Hmid. fwd.
           Search map.split.
           exfalso. apply HSO. eexists (_, _, _, _, _, _). rewrite HO.
           econstructor; eauto.
           destruct ext_spec_ok. intros. eapply unique_mGive_footprint; eauto.
        -- exists O. right. rewrite HO. econstructor; eauto.
           { destruct ext_spec_ok. intros. eapply unique_mGive_footprint; eauto. }
           intros H'. apply not_step. clear not_step. fwd. cbv [state_step step_state] in H'.
           destr_sstate st. inversion H'. subst.
           unify_eval_exprs.
           specialize (H8 _ _ H1). Check map.split_diff.
           destruct (map.split_diff H8 H H6). subst. clear H6 H8. assert (Hmid := H9 _ H1).
           eexists. eexists. eexists. intuition eauto. eapply H9. apply H3.
           Unshelve. (*where did that come from?*) exact (word.of_Z 0).
  Qed.

  Require Import Coq.Logic.ChoiceFacts.

  Lemma enna (A : Type) (P : A -> Prop) :
    (forall y, P y) ->
    ~exists y, ~P y.
  Proof. intros H [y H']. apply H'. apply H. Qed.
  
  Lemma naen (A : Type) (P : A -> Prop) :
    excluded_middle ->
    ~(forall y, P y) ->
    exists y, ~P y.
  Proof.
    clear. cbv [excluded_middle]. intros em H. assert (H1 := em (exists y, ~P y)).
    destruct H1 as [H1|H1].
    - assumption.
    - exfalso. apply H. clear H. intros y. assert (H2 := em (P y)).
      destruct H2 as [H2|H2].
      + assumption.
      + exfalso. apply H1. exists y. assumption.
  Qed.

  Fixpoint repeat_f {A: Type} (f : A -> A) x n :=
    match n with
    | O => x
    | S n' => f (repeat_f f x n')
    end.

  Lemma chains_finite_implies_Acc (A : Type) (R : A -> A -> Prop) x :
    excluded_middle ->
    FunctionalChoice_on A A ->
    (forall f : nat -> A,
        f O = x ->
        ~(forall i, R (f (S i)) (f i))) ->
    Acc R x.
  Proof.
    intros em choice H. cbv [FunctionalChoice_on] in choice.
    specialize (choice (fun x y => ~Acc R x -> ~Acc R y /\ R y x)). destruct choice as [f H'].
    { clear -em. intros x. cbv [excluded_middle] in em.
      assert (H1 := em (forall y : A, R y x -> Acc R y)). destruct H1 as [H1|H1].
      - exists x. intros H. exfalso. apply H. constructor. assumption.
      - assert (H2 := naen). specialize H2 with (1 := em) (2 := H1).
        simpl in H2. destruct H2 as [y H2]. exists y. intros _. split.
        + intros H. apply H2. intros. assumption.
        + assert (H3 := em (R y x)). destruct H3 as [H3|H3].
          -- assumption.
          -- exfalso. apply H2. intros. exfalso. apply H3. apply H. }
    assert (H1 := em (Acc R x)). destruct H1 as [H1|H1].
    - assumption.
    - specialize (H (repeat_f f x) eq_refl).
      assert (H2: forall n, ~ Acc R (repeat_f f x n)).
      { intros n. induction n.
        - apply H1.
        - apply H' in IHn. destruct IHn as [IHn _]. simpl. apply IHn. }
      exfalso. apply H. intros i. specialize (H2 i). apply H' in H2.
      destruct H2 as [_ H2]. simpl. apply H2.
  Qed.

  (*can I define g : sstate -> sstate -> bool such that
    forall s1 s2, comes_right_after_or_prefix s1 s2 -> comes_right_after s1 s2 <-> g s1 s2 = true?*)

  (*A tree of type A is defined as a relation (child : A -> A -> Prop) along with a root
    (head : A)*)

  Definition finite (A : Type) : Prop := exists l, forall (a : A), In a l.
  Definition finitesig {A : Type} (P : A -> Prop) : Prop := exists l, forall a, P a -> In a l.

  (*every infinite graph, where each node has finite nonzero outdegree, contains an infinite path*)
  (*a cycle counts as an infinite path*)
  Lemma Konig {V : Type} (child : V -> V -> Prop) (root : V) :
    (forall v, finitesig (child v) /\ exists v', (child v v')) ->
    (forall f, f O = root -> ~forall k, child (f k) (f (S k))) ->
    finitesig (clos_trans _ child root).
  Admitted.

  Lemma Konigalt {V : Type} (child : V -> V -> Prop) (root : V) :
    (forall v, finitesig (child v) /\ exists v', (child v v')) ->
    ~ finitesig (clos_trans _ child root) ->
    (exists f, f O = root /\ forall k, child (f k) (f (S k))).
  Admitted.

  Section wf_union.
    (*https://www.cs.utexas.edu/users/misra/Notes.dir/ApplicationKoenigLemma.pdf*)
    Context
      {A : Type}
        (R1 R2 : A -> A -> Prop)
        (top1 : A)
        (Htop1 : forall a, R1 top1 a)
        (f : nat -> A)
        (HfO : f O = top1)
        (HfS : forall k, (union _ R1 R2) (f k) (f (S k))).

    Definition transitive {A : Type} (R : A -> A -> Prop) := forall x y z, R x y -> R y z -> R x z.
    Context (trans : transitive (union _ R1 R2)).

    Lemma transitive' i j :
      i < j ->
      (union _ R1 R2) (f i) (f j).
    Proof.
      revert i. induction j.
      - lia.
      - intros. assert (Heqle : i = j \/ i < j) by lia. destruct Heqle as [Heq|Hle].
        + subst. apply HfS.
        + eapply trans.
          -- eapply IHj; assumption.
          -- apply HfS.
    Qed.      

    Check nats_have_mins.

    Definition child (i j : nat) : Prop :=
      R1 (f i) (f j) /\ i < j /\ forall k, i < k < j -> ~R1 (f k) (f j).

    Lemma siblings_totally_ordered_by_R2 i j1 j2 :
      j1 < j2 ->
      child i j1 ->
      child i j2 ->
      R2 (f j1) (f j2).
    Proof.
      intros. assert (H' := transitive' j1 j2 ltac:(assumption)). destruct H' as [H'|H'].
      - cbv [child] in *. fwd. specialize (H1p2 j1 ltac:(lia)). exfalso.
        apply H1p2. apply H'.
      - assumption.
    Qed.

    Lemma parent_exists : forall j, exists i, child i (S j).
    Proof. 
      intros. Check nats_have_mins. assert (H := nats_have_mins j (fun i' => child (j - i') j)).
      exists O. cbv [child]. rewrite HfO. split; [auto|split; [lia|auto]].

    Lemma children_finite : ...

    Lemma false : False.
    Proof.
      

  (*This should be true without choice and middle,
    since all the relevant things have decidable equality.
    But it doesn't seem nice to do it without them,
    and I'm using them elsewhere anyway...*)
  Lemma prefix_dec :
    excluded_middle ->
    FunctionalChoice_on (sstate*sstate) bool ->
    exists dec_prefix, forall s1 s2,
      prefix s1 s2 <-> dec_prefix s1 s2 = true.
  Proof.
    intros em choice. cbv [FunctionalChoice_on] in choice.
    specialize (choice (fun s1_s2 y => let '(s1, s2) := s1_s2 in prefix s1 s2 <-> y = true)).
    simpl in choice. destruct choice as [f f_correct].
    - intros x. specialize (em (let '(s1, s2) := x in prefix s1 s2)). destruct em as [em|em].
      + exists true. destruct x. split; auto.
      + exists false. destruct x. split; auto. congruence.
    - exists (fun s1 s2 => f (s1, s2)). intros. specialize (f_correct (s1, s2)). apply f_correct.
  Qed.

  Fixpoint append_stack (s : scmd) stack :=
    match stack with
    | nil => s
    | s' :: stack' => append_stack (sseq s s') stack'
    end.

  Fixpoint remove_cuts' dec_prefix (f : nat -> sstate) fOcmd stack k :=
    match dec_prefix (f (S O)) (f O) with
    | true =>
        match fOcmd with
        | sseq s1 s2 => remove_cuts' dec_prefix (fun j => f (S j)) s1 (s2 :: stack) k
        | _ => (sskip, nil, nil, map.empty, map.empty, EmptyMetricLog)
        end
    | false =>
        let '(s, k, t, m, l, mc) := f (S k) in
        (append_stack s stack, k, t, m, l, mc)
    end.

  (*I was struggling to find the right generalization of what's going on here.
    This is it:
    https://www.cs.utexas.edu/users/misra/Notes.dir/ApplicationKoenigLemma.pdf
*)
  Lemma remove_cuts'_correct dec_prefix f stack :
    (forall s1 s2, prefix s1 s2 <-> dec_prefix s1 s2 = true) ->
    

  (*given f (infinite seq of comes_right_after_or_prefix),
    returns g (infinite seq of comes_right_after_or_prefix) such that f O steps to g O.*)
  Fixpoint next_seq dec_prefix (f : nat -> sstate) fOcmd k :=
    match dec_prefix (f (S O)) (f O) with
    | true =>
        match fOcmd with
        | sseq s1 s2 =>
            let '(s, k, t, m, l, mc) := next_seq dec_prefix (fun j => f (S j)) s1 k in
            (sseq s s2, k, t, m, l, mc)
        | _ => (sskip, nil, nil, map.empty, map.empty, EmptyMetricLog)
        end
    | false => f (S k)
    end.

  Lemma next_seq_correct dec_prefix f :
    (forall s1 s2, prefix s1 s2 <-> dec_prefix s1 s2 = true) ->
    (forall i, comes_right_after_or_prefix (f (S i)) (f i)) ->
    let g := next_seq dec_prefix f (get_scmd (f O)) in
    (forall i, comes_right_after_or_prefix (g (S i)) (g i)) /\
      comes_right_after (g O) (f O).
  Proof.
    intros Hdec. remember (get_scmd (f O)) as fOcmd eqn:E. revert E. revert f.
    induction fOcmd; intros; simpl in g; subst g; destr_sstate (f O); simpl in E; subst.
    (*this is terrible, should fix*)
    all: try solve [replace (dec_prefix _ _) with false;
              [split;
               [intros; apply H|
                 specialize (H O); rewrite Ef in H; destruct H as [H|H];
                 [assumption|inversion H]]|
                destruct (dec_prefix _ _) eqn:E; [|reflexivity];
                rewrite <- Hdec in E; inversion E]].
    (*just left with the seq case*)
    destruct (dec_prefix _ _) eqn:E.
    - destr_sstate (f (S O)). rewrite <- Hdec in E. inversion E. subst. clear E.
      clear IHfOcmd2. specialize (IHfOcmd1 (fun j => f (S j))).
      simpl in IHfOcmd1. rewrite Ef0 in IHfOcmd1. specialize (IHfOcmd1 eq_refl).
      specialize (IHfOcmd1 (fun i => H (S i))). destruct IHfOcmd1 as [IH1 IH2].
      remember (next_seq dec_prefix (fun j => f (S j))) as g eqn:Eg. clear Eg.
      split.
      + clear IH2. intros i. specialize (IH1 i). destr_sstate (g fOcmd1 (S i)).
        destr_sstate (g fOcmd1 i). destruct IH1 as [IH1|IH1].
        -- left. constructor. apply IH1.
        -- right. inversion IH1. subst. Print prefix. constructor.
        clear Eg. destr_sstate 
        specialize (
      cbv [next_seq] in g. subst g.
    
        

  Lemma steps_with_cuts_to_steps f :
    (forall i, comes_right_after_or_prefix (f (S i)) (f i)) ->
    exists g,
      g O = f O /\
        (forall i, comes_right_after (g (S i)) (g i)).
  Proof. Print comes_right_after_or_prefix. Print prefix.
  (*just remove all the cuts.
    there can only be finitely many in a row, since statements have finite size.*) Admitted.    
  
  Lemma steps_wf s k t m l mc post :
    excluded_middle ->
    FunctionalChoice_on (cmd * trace * io_trace * mem * locals * metrics) (cmd * trace * io_trace * mem * locals * metrics) ->
    (forall (f : nat -> _),
        f O = (inclusion s, k, t, m, l, mc) ->
        possible_execution f ->
        satisfies f post) ->
    Acc lifted_comes_right_after_or_prefix (s, k, t, m, l, mc).
  Proof.
    intros em choice. intros. apply chains_finite_implies_Acc; [apply em|apply choice|].
    clear em choice.
    intros. intros H'. apply steps_with_cuts_to_steps in H'. destruct H' as [g [H'1 H'2] ].
    specialize (H g).
    simpl in H. rewrite H'1 in H. rewrite H0 in H. specialize (H eq_refl). clear H0.
    clear H'1.
    assert (possible_execution g).
    { cbv [possible_execution]. intros. left. apply H'2. }
    apply H in H0.
    destruct H0 as [i H0]. specialize (H'2 i).
    destruct (g i) as [ [ [ [ [si ki] ti] mi] li] mci].
    destruct (g (S i)) as [ [ [ [ [sSi kSi] tSi] mSi] lSi] mcSi].
    simpl in H0. simpl in H'2. destruct H0 as [H0 | H0].
    - destruct H0 as [H0p1 H0p2]. subst. inversion H'2.
    - remember (si, ki, ti, mi, li, mci) as st eqn:Est.
      assert (H'2' : let '(s, k, t, m, l, mc) := st in
                     exists s' k' t' m' l' mc',
                       step s k t m l mc s' k' t' m' l' mc').
      { subst. do 6 eexists. eassumption. }
      clear H'2 Est. induction H0.
      + apply H1. clear H1. fwd. eexists (_, _, _, _, _, _). eassumption.
      + apply H3. clear H3. fwd. eexists (_, _, _, _, _, _). eassumption.
      + apply IHnondet_stuck. clear IHnondet_stuck. fwd. inversion H'2'; subst.
        -- do 6 eexists. eassumption.
        -- inversion H0.
  Qed.

  Lemma done_stable f i :
    possible_execution f ->
    get_scmd (f i) = sskip ->
    forall j,
      f i = f (j + i).
  Proof.
    intros. induction j. (*easy*) Admitted.

  Lemma possible_execution_exists s k t m l mc :
    exists f, f O = (s, k, t, m, l, mc) /\
                possible_execution f.
  Proof. Admitted.

  Lemma step_until_done f i :
    possible_execution f ->
    get_scmd (f i) = sskip ->
    forall j,
      done_state f j \/ step_state f j.
  Proof. Admitted.


  

  Lemma comes_right_after_seq s1 s1' k t m l mc k' t' m' l' mc' s2 :
          lifted_comes_right_after (s1', k', t', m', l', mc') (s1, k, t, m, l, mc) ->
          lifted_comes_right_after (cmd.seq s1' s2, k', t', m', l', mc') (cmd.seq s1 s2, k, t, m, l, mc).
  Proof. Admitted.

  Lemma comes_after_seq s1 s1' k t m l mc k' t' m' l' mc' s2 :
          lifted_comes_after (s1', k', t', m', l', mc') (s1, k, t, m, l, mc) ->
          lifted_comes_after (cmd.seq s1' s2, k', t', m', l', mc') (cmd.seq s1 s2, k, t, m, l, mc).
  Proof. Admitted.
  
  Lemma step_to_exec s k t m l mc post :
    (forall (f : nat -> _),
        f O = (inclusion s, k, t, m, l, mc) ->
        possible_execution f ->
        exists i,
          let '(s', k', t', m', l', mc') := f i in
          s' = sskip /\ post k' t' m' l' mc') ->
    exec s k t m l mc post.
  Proof.
    (*revert post. induction s.
    - intros. econstructor. specialize (H (fun n => (inclusion cmd.skip, k, t, m, l, mc)) eq_refl).
      destruct H as [i H].
      + simpl. cbv [possible_execution]. intros i. right. left. cbv [done_state]. auto.
      + destruct H as [_ H]. assumption.
    - intros. assert (H' := possible_execution_exists (inclusion (cmd.set lhs rhs)) k t m l mc).
      destruct H' as [f [H'1 H'2] ]. specialize (H f H'1 H'2). destruct H as [i H].
      assert (H'' := step_until_done f i). specialize (H'' H'2).
      destruct (f i) as [ [ [ [ [s' k'] t'] m'] l'] mc'] eqn:Ei. fwd. specialize (H'' eq_refl).
      specialize (H'' O). destruct H'' as [H'' | H''].
      + cbv [done_state] in H''. rewrite H'1 in H''. simpl in H''. destruct H'' as [H'' _].
        congruence.
      + cbv [step_state state_step] in H''. rewrite H'1 in H''.
        destruct (f 1%nat) as [ [ [ [ [s2 k2] t2] m2] l2] mc2] eqn:E1. inversion H''. subst.
        econstructor; try eassumption. Search i. destruct i.
        -- rewrite Ei in H'1. simpl in H'1. congruence.
        -- assert (H' := done_stable f 1 H'2). rewrite E1 in H'. specialize (H' eq_refl).
           specialize (H' i). replace (i + 1) with (S i) in * by lia. rewrite Ei in H'.
           inversion H'. subst. assumption.
    - admit.
    - admit.
    - admit.
    - admit.
    - intros post H. assert (H' := H). apply steps_wf in H'. apply Acc_clos_trans in H'.
      fold comes_after in H'. revert H. revert post.
      eapply (@Fix_F _ _ (fun x => let '(_, _, _, _, _, _) := x in _) _ _ H').
      Unshelve. simpl. clear. intros. destruct x as [ [ [ [ [s k] t] m] l] mc]. intros.
      revert X. revert H. revert post.*)

    (*here's how it goes when we try execution order, then command structure.*)
    intros H. assert (H' := H). apply steps_wf in H'. apply Acc_clos_trans in H'.
    fold lifted_comes_after_or_prefix in H'. (*fix this.*)
    revert H. revert post.
    eapply (@Fix_F _ _ (fun x => let '(_, _, _, _, _, _) := x in _) _ _ H').
    Unshelve. simpl. clear. intros. destruct x as [ [ [ [ [s k] t] m] l] mc]. intros.
    revert X. revert H. revert post.
    destruct s.
    - econstructor. specialize (H (fun n => (inclusion cmd.skip, k, t, m, l, mc)) eq_refl).
      destruct H as [i H].
      + simpl. cbv [possible_execution]. intros i. right. left. cbv [done_state]. auto.
      + destruct H as [_ H]. assumption.
    - intros. assert (H' := possible_execution_exists (inclusion (cmd.set lhs rhs)) k t m l mc).
      destruct H' as [f [H'1 H'2] ]. specialize (H f H'1 H'2). destruct H as [i H].
      assert (H'' := step_until_done f i). specialize (H'' H'2).
      destruct (f i) as [ [ [ [ [s' k'] t'] m'] l'] mc'] eqn:Ei. fwd. specialize (H'' eq_refl).
      specialize (H'' O). destruct H'' as [H'' | H''].
      + cbv [done_state] in H''. rewrite H'1 in H''. simpl in H''. destruct H'' as [H'' _].
        congruence.
      + cbv [step_state state_step] in H''. rewrite H'1 in H''.
        destruct (f 1%nat) as [ [ [ [ [s2 k2] t2] m2] l2] mc2] eqn:E1. inversion H''. subst.
        econstructor; try eassumption. Search i. destruct i.
        -- rewrite Ei in H'1. simpl in H'1. congruence.
        -- assert (H' := done_stable f 1 H'2). rewrite E1 in H'. specialize (H' eq_refl).
           specialize (H' i). replace (i + 1) with (S i) in * by lia. rewrite Ei in H'.
           inversion H'. subst. assumption.
    - admit.
    - admit.
    - admit.
    - admit.
    - intros. Check invert_seq. assert (H' := invert_seq _ _ _ _ _ _ _ _ H). fold inclusion in *.
      econstructor.
      + eapply (X (s1, k, t, m, l, mc)).
        -- cbv [comes_after_or_prefix]. Print clos_trans. apply t_step.
           cbv [comes_right_after_or_prefix]. right. constructor.
        -- apply H'.
      + simpl. intros. destruct H0 as [H1 H2]. eapply (X (s2, k', t', m', l', mc')).
        -- (*easy, use H1*) admit.
        -- apply H2.
    - 
          
      assert (Hs1 := X (s1, k, t, m, l, mc)).
      assert (H0 : comes_after_or_prefix (s1, k, t, m, l, mc) (cmd.seq s1 s2, k, t, m, l, mc)).
      {  }
      specialize (Hs1 H0). clear H0. simpl in Hs1.
      
      edestruct Hs1. specialize Hs1 with (1 := ltac:(dconstructor)). econstructor.
      + apply IHs1. intros. destruct y as [ [ [ [ [ s1' k' ] t' ] m' ] l' ] mc' ].
        eapply comes_after_seq in H0. apply X in H0. intros post'.
        intros H''.
        specialize (H0 post').

        
      

      
        exists i,
          let '(s', k', t', m', l', mc') := f i in
          s' = s2 /\ forall
      econstructor.
           simpl in H'.
           eapply done_stable in H'2. rewriet H'2 in E. cbv [possible_execution] in H'2.
      
      + instantiate (1 := fun n => match n with | O => _ | _ => _ end). reflexivity.
      + cbv [possible_execution]. intros i. destruct i as [| i].
        * simpl. left. cbv [step_state state_step]. instantiate (1 := (_, _, _, _, _, _)).
          simpl. econstructor.
      specialize (H (fun n =>
                       match n with
                       | O => _
                       | _ => _ end) eq_refl).
      destruct H as [i H].
      + simpl. cbv [possible_execution]. intros i. right. left. cbv [done_state]. auto.
      + destruct H as [_ H]. assumption.
      
      with (3 := H').
    2: eapply 






      assert (HSO := HS O). destruct HSO as [HSO | [HSO | HSO] ].
      + exists (S O). cbv [step_state state_step] in HSO.
        destruct (f (S O)) as [ [ [ [ [s2 k2] t2] m2] l2] mc2]. rewrite HO in HSO.
        inversion HSO. subst.
        
        reflexivity.
      + exists O. cbv [done_state] in HSO. destruct HSO as [HSO _]. assumption.
      + exfalso. apply HSO. eexists (_, _, _, _, _, _). rewrite HO. cbv [state_step].
        econstructor; eassumption.
    - intros. assert (H3 := H2 O). destruct H3 as [H3 | [H3 | H3] ].
      + exists (S O). cbv [step_state state_step] in H3.
        destruct (f (S O)) as [ [ [ [ [s2 k2] t2] m2] l2] mc2]. rewrite H1 in H3.
        inversion H3. subst. reflexivity.
      + exists O. cbv [done_state] in H3. destruct H3 as [H3 _]. assumption.
      + exfalso. apply H3. eexists (_, _, _, _, _, _). rewrite H1. cbv [state_step].
        constructor. eassumption.
        simpl in H3.
        destruct ( cbv [step_state state_step] in H3.
      rewrite H1 in H3. destruct H3 as [ H3 | H3 | H3 ].
      + exists (S O). simpl in H3. 
        inversion H3. subst. reflexivity.
      + simpl in H3. destruct H3 as [H3p1 H3p2]. simpl in H3p1. congruence.
    - intros. assert (H2 := H1 O). rewrite H0 in H2. destruct H2 as [H2 | H2].
      + exists (S O). simpl in H2. destruct (f (S O)) as [ [ [ [ [s2 k2] t2] m2] l2] mc2].
        inversion H2. subst. reflexivity.
      + simpl in H2. destruct H2 as [H2p1 H2p2]. simpl in H2p1. congruence.
    - intros. assert (H5 := H4 O). rewrite H3 in H5. destruct H5 as [H5 | H5].
      + exists (S O). simpl in H5. destruct (f (S O)) as [ [ [ [ [s2 k2] t2] m2] l2] mc2].
        inversion H5. subst. reflexivity.
      + simpl in H5. destruct H5 as [H5p1 H5p2]. simpl in H5p1. congruence.
        
        cbv [state_done] in H3. simpl in H3.
        
      destruct H

      assert (H2 := H1 O). rewrite H0 in H2. destruct H2 as [H2 | H2].
      + 
      eexists.


  Lemma weaken: forall s k t m l mc post1,
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

  Lemma intersect: forall k t l m mc s post1,
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

  Lemma exec_to_other_trace s k1 k2 t m l mc post :
    exec s k1 t m l mc post ->
    exec s k2 t m l mc (fun k2' t' m' l' mc' =>
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
    - econstructor; intuition. eapply weaken. 1: eapply H1; eauto.
      simpl. intros. fwd. exists mSmall', mStack'. intuition. eexists (_ ++ _ :: nil).
      repeat rewrite <- (app_assoc _ _ k2). repeat rewrite <- (app_assoc _ _ k).
      intuition.
    - apply expr_to_other_trace in H. fwd. eapply if_true; intuition eauto.
      eapply weaken. 1: eapply IHexec. simpl. intros. fwd. eexists (_ ++ _ :: _).
      repeat rewrite <- (app_assoc _ _ k2). repeat rewrite <- (app_assoc _ _ k).
      intuition.
    - apply expr_to_other_trace in H. fwd. eapply if_false; intuition.
      eapply weaken. 1: eapply IHexec. simpl. intros. fwd. eexists (_ ++ _ :: _).
      repeat rewrite <- (app_assoc _ _ k2). repeat rewrite <- (app_assoc _ _ k).
      intuition.
    - econstructor; intuition. fwd. eapply weaken. 1: eapply H1; eauto.
      simpl. intros. fwd. eexists (_ ++ _).
      repeat rewrite <- (app_assoc _ _ k2). repeat rewrite <- (app_assoc _ _ k).
      intuition.
    - apply expr_to_other_trace in H. fwd. eapply while_false; intuition.
      eexists (_ :: _). intuition.
    - apply expr_to_other_trace in H. fwd. eapply while_true; intuition. fwd.
      eapply weaken. 1: eapply H3; eauto. simpl. intros. fwd. eexists (_ ++ _ ++ _ :: _).
      repeat rewrite <- (app_assoc _ _ k2). repeat rewrite <- (app_assoc _ _ k).
      intuition.
    - Search evaluate_call_args_log. apply call_args_to_other_trace in H0.
      fwd. econstructor; intuition eauto. fwd. apply H3 in H0p2.
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
        exec body (consume_word a :: k)(*don't need this here - I leave it for consistency with other semantics*) t mCombined (map.put l x a) (addMetricInstructions 1 (addMetricLoads 1 mc))
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

  Lemma weaken {pick_sp : PickSp} : forall s k t m l mc post1,
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

  Lemma intersect {pick_sp : PickSp} : forall k t l m mc s post1,
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

  Lemma otherexec_extends_trace {pick_sp: PickSp} s k t m l mc post :
    exec s k t m l mc post ->
    exec s k t m l mc (fun k' t' m' l' mc' => post k' t' m' l' mc' /\ exists k'', k' = k'' ++ k).
  Proof.
    intros H. induction H; try (econstructor; intuition eauto; subst_exprs; eexists; trace_alignment; fail).
    - econstructor; intuition eauto. intros. eapply weaken. 1: eapply H1; eauto.
      simpl. intros. intuition eauto. fwd. eexists. eexists. intuition eauto.
      eexists. trace_alignment.
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
  End WithEnv.
End otherexec. Notation otherexec := otherexec.exec.
Check exec.



Module two_execs. Section WithEnv.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word byte}.
  Context {locals: map.map String.string word}.
  Context {env: map.map String.string (list String.string * list String.string * cmd)}.
  Context {ext_spec: ExtSpec}.
  Context (e: env).

  Local Notation metrics := MetricLog.

  Implicit Types post : trace -> io_trace -> mem -> locals -> metrics -> Prop. (* COQBUG(unification finds Type instead of Prop and fails to downgrade *)
  Check exec.

  

  Ltac solve_stuff := econstructor; intuition eauto; subst_exprs; try (eexists; split; [trace_alignment|]); eauto.

  Lemma is_this_even_provable :
    forall e k t l m mc s post,
      (forall pick_sp, otherexec (pick_sp := pick_sp) e s k t m l mc (fun _ _ _ _ _ => True)) ->
      exec e s k t m l mc (fun _ _ _ _ _ => True).
  Proof.
    intros. destruct s. 
    - solve_stuff.
    - specialize (H (fun _ => word.of_Z 0)). inversion H. subst. solve_stuff.
    - specialize (H (fun _ => word.of_Z 0)). inversion H. subst. solve_stuff.
    - specialize (H (fun _ => word.of_Z 0)). inversion H. subst. solve_stuff.
    - econstructor.
      + specialize (H (fun _ => word.of_Z 0)). inversion H. subst. assumption.
      + intros.
  Abort.

  Lemma append_thing {A : Type} (l1 l2 : list A) :
    l1 = l2 ++ l1 ->
    l2 = nil.
  Proof.
    intros H. remember (l2 ++ l1) as x. replace l1 with (nil ++ l1) in H by reflexivity.
    subst. apply app_inv_tail in H. subst. reflexivity.
  Qed.

  Search predicts.
  Lemma predicts_trivially k :
    (forall x, ~In (consume_word x) k) ->
    forall f,
      predicts f k.
  Proof.
    induction k; constructor.
    - intros Ha. destruct a; destruct Ha. simpl in H. specialize (H r). tauto.
    - apply IHk. intros x Hx. eapply H. simpl. right. eassumption.
  Qed.

  Lemma fold_app : (fix app (l m0 : list event) {struct l} : list event :=
                      match l with
                      | nil => m0
                      | a1 :: l1 => a1 :: app l1 m0
                      end) = @List.app event.
  Proof. reflexivity. Qed.

  Lemma predicts_app k1 k2 f :
    predicts f k1 ->
    predicts (fun k => f (k1 ++ k)) k2 ->
    predicts f (k1 ++ k2).
  Proof.
    revert k2. revert f. induction k1.
    - intros. assumption.
    - intros. inversion H. subst. clear H. constructor.
      + assumption.
      + rewrite fold_app. apply IHk1; assumption.
  Qed.
      
  Lemma execs_related' pick_sp k t l m mc s post' :
    exec e s k t m l mc post' ->
    forall post,
      (forall k' t' m' l' mc',
          post' k' t' m' l' mc' ->
          forall k'',
            k' = k'' ++ k ->
            predicts (fun k_ => consume_word (pick_sp (rev k_ ++ k))) (List.rev k'') ->
            post k' t' m' l' mc') ->
      otherexec (pick_sp := pick_sp) e s k t m l mc post.
  Proof.
    intros H. induction H.
    - solve_stuff. eapply H0; [auto | trace_alignment | constructor].
    - solve_stuff. eapply H1; [auto | trace_alignment | ].
      apply predicts_trivially. intros x1. specialize (H2 x1).
      rewrite <- in_rev. rewrite app_nil_r. assumption.
    - solve_stuff. eapply H0; [auto | trace_alignment | constructor].
    - solve_stuff. eapply H3; [auto | trace_alignment | ].
      apply predicts_trivially. intros x1 Hx1. rewrite <- in_rev in Hx1.
      destruct Hx1 as [Hx1|Hx1]; [congruence|]. rewrite app_nil_r in Hx1.
      apply in_app_or in Hx1. destruct Hx1; intuition eauto.
    - solve_stuff. intros.
      eapply H1; try eassumption. intros. fwd. subst. eexists. eexists. intuition eauto.
      eapply H2; [auto | trace_alignment | ]. rewrite rev_app_distr. simpl. constructor.
      + intros _. reflexivity.
      + simpl. eapply predicts_ext. 2: eapply H7. simpl. intros. rewrite <- app_assoc.
        reflexivity.
    - solve_stuff. eapply IHexec; try eassumption. intros. subst.
      eapply H2; [auto | trace_alignment | ]. rewrite app_nil_r. rewrite rev_app_distr.
      simpl. rewrite <- app_assoc. simpl. apply predicts_app.
      + apply predicts_trivially. intros x0. rewrite <- in_rev. auto.
      + constructor.
        -- intros [].
        -- eapply predicts_ext. 2: eapply H5. simpl. intros. rewrite rev_app_distr.
           rewrite rev_involutive. simpl. repeat rewrite <- app_assoc. simpl. reflexivity.
    - intros.
      (*solve_stuff*)eapply otherexec.if_false; intuition eauto; subst_exprs; try (eexists; split; [trace_alignment|]); eauto.
      eapply IHexec; try eassumption. intros. subst.
      eapply H2; [auto | trace_alignment | ]. rewrite app_nil_r. rewrite rev_app_distr.
      simpl. rewrite <- app_assoc. simpl. apply predicts_app.
      + apply predicts_trivially. intros x0. rewrite <- in_rev. auto.
      + constructor.
        -- intros [].
        -- eapply predicts_ext. 2: eapply H5. simpl. intros. rewrite rev_app_distr.
           rewrite rev_involutive. simpl. repeat rewrite <- app_assoc. simpl. reflexivity.
    - econstructor. Check otherexec.otherexec_extends_trace.
      1: eapply otherexec.otherexec_extends_trace.
      1: { eapply IHexec. intros. instantiate
          (1 := fun k' t' m' l' mc' =>
                  forall k'',
                    k' = k'' ++ k ->
                    predicts (fun k_ : trace => consume_word (pick_sp (rev k_ ++ k))) (rev k'') /\
                      mid k' t' m' l' mc'). simpl. intuition eauto. subst.
           apply app_inv_tail in H6. subst. assumption. }
      simpl. intros. fwd. specialize (H3p0 _ eq_refl). fwd.
      eapply H1; try eassumption. intros. subst.
      eapply H2; [auto | trace_alignment | ].
      rewrite app_nil_r. rewrite rev_app_distr. apply predicts_app.
      + assumption.
      + eapply predicts_ext. 2: eapply H5. simpl. intros. rewrite rev_app_distr.
        rewrite rev_involutive. rewrite <- app_assoc. reflexivity.
    - solve_stuff. eapply H2; [auto | trace_alignment | ].
      rewrite app_nil_r. simpl. apply predicts_app.
      + apply predicts_trivially. intros x0. rewrite <- in_rev. auto.
      + constructor; [intros []|]. constructor.
    - intros. eapply otherexec.while_true; [eassumption|eassumption| | ].
      { eapply otherexec.otherexec_extends_trace. eapply IHexec. intros. instantiate
          (1 := fun k'0 t'0 m'0 l'0 mc'0 =>
                  forall k''0,
                    k'0 = k''0 ++ leak_bool true :: k' ->
                    predicts (fun k_ : trace => consume_word (pick_sp (rev k_ ++ (leak_bool true :: k')))) (rev k''0) /\
                      mid k'0 t'0 m'0 l'0 mc'0).
        simpl. intuition eauto. subst. apply app_inv_tail in H8. subst. auto. }
      simpl. intros. fwd. specialize (H5p0 _ eq_refl). fwd.
      eapply H3; try eassumption. intros. subst. subst_exprs.
      eapply H4; [auto | trace_alignment | ]. rewrite app_nil_r.
      repeat rewrite rev_app_distr. repeat rewrite <- app_assoc. simpl.
      apply predicts_app.
      + apply predicts_trivially. intros x0 Hx0. apply in_app_or in Hx0. destruct Hx0 as [Hx0|Hx0].
        -- rewrite <- in_rev in Hx0. eapply H6. eapply Hx0.
        -- simpl in Hx0. destruct Hx0; [congruence|assumption].
      + apply predicts_app.
        -- eapply predicts_ext. 2: eapply H5p0p0. simpl. intros. repeat rewrite rev_app_distr.
           rewrite rev_involutive. repeat rewrite <- app_assoc. simpl. reflexivity.
        -- eapply predicts_ext. 2: eapply H7. simpl. intros. repeat rewrite rev_app_distr.
           repeat rewrite rev_involutive. repeat rewrite <- app_assoc. simpl. reflexivity.
    - econstructor; [eassumption | eassumption | eassumption | |].
      { eapply otherexec.otherexec_extends_trace. eapply IHexec. intros. instantiate
          (1 := fun k'0 t'0 m'0 l'0 mc'0 =>
                  forall k''0,
                    k'0 = k''0 ++ leak_unit :: k' ->
                    predicts (fun k_ : trace => consume_word (pick_sp (rev k_ ++ (leak_unit :: k')))) (rev k''0) /\
                      mid k'0 t'0 m'0 l'0 mc'0).
        simpl. intuition eauto. subst. apply app_inv_tail in H8. subst. auto. }
      simpl. intros. intuition eauto. fwd. specialize (H6 _ eq_refl). fwd.
      apply H3 in H6p1. fwd. eexists. intuition eauto.
      eexists. intuition eauto. subst_exprs.
      eapply H4; [auto | trace_alignment | ].
      rewrite app_nil_r. rewrite rev_app_distr. simpl. apply predicts_app.
      + apply predicts_trivially. intros x0 Hx0. apply in_app_or in Hx0. destruct Hx0 as [Hx0|Hx0].
        -- rewrite <- in_rev in Hx0. apply H5 in Hx0. assumption.
        -- destruct Hx0; [congruence|assumption].
      + eapply predicts_ext. 2: eapply H6p0. simpl. intros. repeat rewrite rev_app_distr.
        simpl. rewrite rev_involutive. repeat rewrite <- app_assoc. simpl. reflexivity.
    - econstructor; intuition eauto. apply H2 in H4. fwd. eexists. intuition eauto. subst_exprs.
      eapply H3; [auto | trace_alignment | ]. rewrite app_nil_r. simpl.
      apply predicts_trivially. intros x0 Hx0. apply in_app_or in Hx0. destruct Hx0 as [Hx0|Hx0].
      + rewrite <- in_rev in Hx0. apply H5 in Hx0. assumption.
      + destruct Hx0; [congruence|assumption].
  Qed.

  Lemma execs_related pick_sp k t l m mc s post :
    exec e s k t m l mc (fun k' t' m' l' mc' =>
                           exists k'',
                             k' = k'' ++ k /\
                               (predicts (fun k_ => consume_word (pick_sp (rev k_ ++ k))) (List.rev k'') ->
                                post k' t' m' l' mc')) ->
    otherexec (pick_sp := pick_sp) e s k t m l mc post.
  Proof.
    intros. eapply execs_related' in H. 1: eassumption. intros. fwd.
    apply app_inv_tail in H1. subst. apply H0p1. apply H2.
  Qed.

  Lemma execs_related_rephrased k t l m mc s post :
    (forall pick_sp,
        exec e s k t m l mc (fun k' t' m' l' mc' =>
                               exists k'',
                                 k' = k'' ++ k /\
                                   (predicts pick_sp (List.rev k'') ->
                                    post k' t' m' l' mc'))) ->
    (forall pick_sp, otherexec (pick_sp := pick_sp) e s k t m l mc post).
  Proof. intros. apply execs_related. apply H. Qed.
