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
Require Import Coq.Classes.Morphisms.

  Require Import Coq.Wellfounded.Union.
  Require Import Relation_Operators.
  Require Import Relation_Definitions.
  Require Import Transitive_Closure.
  Require Import Coq.Logic.ChoiceFacts.

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

    intersect: forall t mGive a args,
      ext_spec t mGive a args (fun mReceive resvals klist =>
                                 forall mid, ext_spec t mGive a args mid ->
                                             mid mReceive resvals klist);
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

Ltac subst_exprs :=
  repeat match goal with
    | H : eval_expr _ _ _ _ _ = Some _ |- _ =>
        apply eval_expr_extends_trace in H; destruct H as [? [? ?] ]; subst
    | H : evaluate_call_args_log _ _ _ _ _ = Some _ |- _ =>
        apply evaluate_call_args_log_extends_trace in H; destruct H as [? [? ?] ]; subst
    end.

Require Import Lia.

Module exec. Section WithEnv.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word byte}.
  Context {locals: map.map String.string word}.
  Context {env: map.map String.string (list String.string * list String.string * cmd)}.
  Context {ext_spec: ExtSpec}.
  Context (e: env).
  Local Notation metrics := MetricLog.

  Section WithDet.
    Context {pick_sp : PickSp}.
    Context (salloc_det : bool).

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
        (salloc_det = true -> a = pick_sp k) ->
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
          (*it is a mystery to me why we treat l' and m' differently here.
            why not both having the exists quantifier?  or both having the forall?*)
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
  | end_stackalloc (nbytes : Z) (a : word)
  (* { lhs = alloca(nbytes); body; /*allocated memory freed right here*/ } *)
  | scond (condition : expr) (nonzero_branch zero_branch : scmd)
  | sseq (s1 s2: scmd)
  | swhile (test : expr) (body : scmd)
  | jump_back
  | scall (binds : list String.string) (function : String.string) (args: list expr)
  | start_call (binds : list String.string) (params : list String.string) (rets: list String.string) (fbody: scmd) (args: list expr)
  | end_call (binds : list String.string) (rets: list String.string) (l : locals)
  | sinteract (binds : list String.string) (action : String.string) (args: list expr)
  | end_interact (binds : list String.string) (action : String.string) (args : list word) (mKeep mGive mReceive : mem) (resvals klist : list word).
  
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
      k t mSmall l mc
      mStack mCombined
      (_ : Z.modulo n (bytes_per_word width) = 0)
      (_ : salloc_det = true -> a = pick_sp k)
      (_ : anybytes a n mStack)
      (_ : map.split mCombined mSmall mStack)
    : step (sstackalloc x n body) k t mSmall l mc
        (sseq body (end_stackalloc n a)) (consume_word a :: k) t mCombined (map.put l x a) (ami 1 (aml 1 mc))
  | stackalloc_end_step n a
      k t mCombined l mc
      mSmall mStack
      (_ : anybytes a n mStack)
      (_ : map.split mCombined mSmall mStack)
    : step (end_stackalloc n a) k t mCombined l mc
        sskip k t mSmall l mc
  | if_true_step k t m l mc e c1 c2
    v mc' k' (_ : eval_expr m l e mc k = Some (v, mc', k'))
    (_ : word.unsigned v <> 0)
    : step (scond e c1 c2) k t m l mc
        c1 (leak_bool true :: k') t m l (ami 2 (aml 2 (amj 1 mc')))
  | if_false_step k t m l mc e c1 c2
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
      (_ : ext_spec t mGive action args (fun _ _ _ => True))
      mReceive resvals klist
      (_ : forall mid, ext_spec t mGive action args mid -> mid mReceive resvals klist)
    : step (sinteract binds action arges) k t m l mc
           (end_interact binds action args mKeep mGive mReceive resvals klist) k' t m l mc'
  | end_interact_step (binds : list String.string) (action : String.string) (args : list word)
      (k' : trace) (mc' : MetricLog) (mKeep mGive mReceive : mem) (resvals klist : list word)
      k t m l mc
      l' (_ : map.putmany_of_list_zip binds resvals l = Some l')
      m' (_ : map.split m' mKeep mReceive)
    : step (end_interact binds action args mKeep mGive mReceive resvals klist) k t m l mc
        sskip (leak_list klist :: k)%list (((mGive, action, args), (mReceive, resvals)) :: t) m' l' (ami 1 (ams 1 (aml 2 mc))).

  Definition sstate : Type := scmd * trace * io_trace * mem * locals * metrics.
  Definition get_scmd (st : sstate) : scmd :=
    let '(s, k, t, m, l, mc) := st in s.

  Definition other_inclusion st : sstate :=
    let '(s, k, t, m, l, mc) := st in
    (inclusion s, k, t, m, l, mc).

  Definition state_step st st' : Prop :=
    let '(s, k, t, m, l, mc) := st in
    let '(s', k', t', m', l', mc') := st' in
    step s k t m l mc s' k' t' m' l' mc'.

  (*Definition done_state f i :=
    get_scmd (f i) = sskip /\ get_scmd (f (S i)) = terminated.*)

  Definition o1 {X : Type} (R : X -> Prop) (x : option X) : Prop :=
    match x with
    | Some x => R x
    | _ => False
    end.

  Definition o2 {X Y : Type} (R : X -> Y -> Prop) x y : Prop :=
    match x, y with
    | Some x, Some y => R x y
    | _, _ => False
    end.

  Definition state_stuck st :=
    ~exists st', state_step st st'.

  Definition stuck_ostate f i :=
    o1 state_stuck (f i) /\ f (S i) = None.

  Definition step_ostate f i :=
    o2 state_step (f i) (f (S i)).

  Definition possible_execution (f : nat -> option sstate) :=
    forall i, step_ostate f i \/ stuck_ostate f i \/ f i = None /\ f (S i) = None.

  Inductive good_stuck : sstate -> Prop :=
  | good_stuck_stackalloc : forall k t m l mc x n body,
      Z.modulo n (bytes_per_word width) = 0 ->
      state_stuck (sstackalloc x n body, k, t, m, l, mc) ->
      good_stuck (sstackalloc x n body, k, t, m, l, mc)
  | good_stuck_interact : forall k t m l mc binds action arges mKeep mGive args mc' k',
      map.split m mKeep mGive ->
      evaluate_call_args_log m l arges mc k = Some (args, mc', k') ->
      ext_spec t mGive action args (fun _ _ _ => True) ->
      state_stuck (sinteract binds action arges, k, t, m, l, mc) ->
      good_stuck (sinteract binds action arges, k, t, m, l, mc)
  | good_stuck_end_interact : forall k t m l mc binds action args mKeep mGive mReceive resvals klist,
      (*I don't think there's any principled reason to have the l' condition here
        but not the m' condition.  just the way exec was written.*)
      (exists l', map.putmany_of_list_zip binds resvals l = Some l') ->
      state_stuck (end_interact binds action args mKeep mGive mReceive resvals klist, k, t, m, l, mc) ->
      good_stuck (end_interact binds action args mKeep mGive mReceive resvals klist, k, t, m, l, mc)
  | good_stuck_seq : forall s1 s2 k t m l mc,
    good_stuck (s1, k, t, m, l, mc) ->
    good_stuck (sseq s1 s2, k, t, m, l, mc).

  Definition state_satisfies post st : Prop :=
    (let '(s, k, t, m, l, mc) := st in s = sskip /\ post k t m l mc) \/
      good_stuck st.

  Definition satisfies (f : nat -> _) post := exists i, o1 (state_satisfies post) (f i).
  
  Definition comes_right_after s1 s2 :=
    state_step s2 s1. Check pointwise_relation. Search (relation _ -> relation _).
  Definition lift {A B : Type} (R : relation B) (f : A -> B) : relation A :=
    fun x y => R (f x) (f y).
  Definition lifted_comes_right_after := lift comes_right_after other_inclusion.
  Inductive prefix : sstate -> sstate -> Prop :=
  | bprefix : forall s1 s2 k t m l mc,
      prefix (s1, k, t, m, l, mc) (sseq s1 s2, k, t, m, l, mc).

  (*Definition comes_right_after_or_prefix := union _ prefix comes_right_after.*)
  
  (*Definition lifted_comes_right_after_or_prefix := lift comes_right_after_or_prefix other_inclusion.*)

  Definition repeated_prefix := clos_trans _ prefix.
  Definition comes_after := clos_trans _ comes_right_after.
  Definition lifted_comes_after := lift comes_after other_inclusion.

  Definition comes_after_or_repeated_prefix := clos_trans _ (union _ repeated_prefix comes_after).
  Definition lifted_comes_after_or_repeated_prefix := lift comes_after_or_repeated_prefix other_inclusion.

  Definition first_part st : option sstate :=
    match st with
    | Some (sseq s1 s2, k, t, m, l, mc) => Some (s1, k, t, m, l, mc)
    | _ => None (*this is just some dummy value here*)
    end.
  
  Fixpoint execution_of_first_part (f : nat -> option sstate) n :=
    match n with
    | O => first_part (f O)
    | S n' =>
        match (execution_of_first_part f n') with
        | Some (sskip, _, _, _, _, _) => None
        | None => None
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

  Section choice_and_middle.
    Context
      (em : excluded_middle)
        (choice : FunctionalChoice_on (option sstate) (option sstate)).

  Lemma sskip_or_first_part' f n :
    match (execution_of_first_part f n) with
    | Some (sskip, _, _, _, _, _) => True
    | None => True
    | _ => first_part (f n) = execution_of_first_part f n
    end.
  Proof.
    destruct n.
    - simpl. destruct (f O) as [st|]; [|reflexivity]. destr_sstate st.
      destruct s; try reflexivity. simpl. destruct s1; eexists; reflexivity.
    - simpl. destruct (execution_of_first_part f n) as [st|]; [|reflexivity].
      destr_sstate st. destruct s; try reflexivity.
      all: destruct (first_part (f (S n))) as [st'|]; [|reflexivity].
      all: destr_sstate st'; destruct s; try reflexivity.
      all: destruct s0; reflexivity.
  Qed.

  Lemma sskip_terminated_or_first_part f n :
    option_map get_scmd (execution_of_first_part f n) = Some sskip \/ execution_of_first_part f n = None \/ first_part (f n) = execution_of_first_part f n.
  Proof.
    assert (H := sskip_or_first_part' f n). destruct (execution_of_first_part f n) as [st|]; auto.
    destr_sstate st. destruct s; auto.
  Qed.
  
  Lemma possible_first_part f :
    possible_execution f ->
    possible_execution (execution_of_first_part f).
  Proof.
    cbv [possible_execution]. intros H n.
    specialize (H n). assert (H1 := sskip_terminated_or_first_part f n).
    destruct H1 as [H1 | [H1 | H1]].
    - cbv [step_ostate stuck_ostate].
      destruct (execution_of_first_part f n) as [st|] eqn:E; simpl in H1. 2: congruence.
      destr_sstate st. simpl in H1. inversion H1. clear H1. subst.
      right. left. split.
      + simpl. intros [st H']. destr_sstate st. inversion H'.
      + simpl. rewrite E. reflexivity.
    - right. right. simpl. rewrite H1. auto.
    - destruct (execution_of_first_part f n) as [s_s2|] eqn:Ebig.
      2: { simpl. rewrite Ebig. auto. }
      destruct H as [H | [H | H]].
      + cbv [step_ostate] in H.
        destruct (f n) as [s|] eqn:E, (f (S n)) as [s'|] eqn:E'; simpl in H; try destruct H as [].
        destr_sstate s. destr_sstate s'. subst.
        destruct s0; simpl in H1; try congruence. inversion H1; clear H1; subst.
        inversion H; subst.
        -- left. cbv [step_ostate]. simpl. rewrite Ebig. rewrite E'. simpl.
           destruct s0_1; try assumption. inversion H13.
        -- right. left. cbv [stuck_ostate]. split.
           2: { simpl. rewrite Ebig. reflexivity. }
           rewrite Ebig. simpl. intros [st' H']. destr_sstate st'. inversion H'.
      + right. left. destruct H as [Hp1 Hp2]. split.
        -- destruct (f n) as [st|]; try solve [destruct Hp1]. destr_sstate st.
           destruct s; simpl in H1; try congruence. inversion H1; clear H1; subst.
           rewrite Ebig. simpl. intros [st' H']. apply Hp1. destr_sstate st'.
           eexists (_, _, _, _, _, _). eapply seq_step. eassumption.
        -- simpl. rewrite Ebig. rewrite Hp2. destr_sstate (s_s2). destruct s; reflexivity.
      + exfalso. fwd.
        destruct n as [|n]; simpl in Ebig; rewrite Hp0 in Ebig; simpl in Ebig; try congruence.
        destruct (execution_of_first_part f n) as [st|]; try congruence.
        destr_sstate st. destruct s; congruence.
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

  Lemma good_stuck_stuck st :
    good_stuck st ->
    state_stuck st.
  Proof.
    intros H. induction H; auto. intros H'. apply IHgood_stuck.
    destruct H' as [st' H']. destr_sstate st'. inversion H'; subst.
    - eexists (_, _, _, _, _, _). eassumption.
    - inversion H.
  Qed.

  Lemma satisfies_stuck st post :
    state_satisfies post st ->
    state_stuck st.
  Proof.
    intros. destr_sstate st. destruct H as [H|H].
    - fwd. intros [st' H']. destr_sstate st'. inversion H'.
    - apply good_stuck_stuck. assumption.
  Qed.

  Lemma step_not_stuck st st' :
    state_step st st' ->
    state_stuck st ->
    False.
  Proof.
    intros H H'.
    cbv [state_step state_stuck] in *. apply H'. destr_sstate st. destr_sstate st'.
    eexists (_, _, _, _, _, _). eassumption.
  Qed.

  Lemma done_stable f n :
    possible_execution f ->
    f n = None ->
    forall m, n <= m ->
              f m = None.
  Proof.
    intros H1 H2 m Hm. induction m.
    - assert (n = O) by lia. subst. assumption.
    - destruct (Nat.leb n m) eqn:E.
      + apply PeanoNat.Nat.leb_le in E. specialize (IHm E). specialize (H1 m).
        destruct H1 as [H1|[H1|H1]].
        { cbv [step_ostate] in H1. rewrite IHm in H1. simpl in H1. destruct H1. }
        { cbv [stuck_ostate] in H1. rewrite IHm in H1. simpl in H1. fwd. destruct H1p0. }
        fwd. assumption.
      + apply PeanoNat.Nat.leb_nle in E. assert (n = S m) by lia. subst. assumption.
  Qed.

  Lemma state_stuck_stuck_state f n :
    possible_execution f ->
    o1 state_stuck (f n) ->
    stuck_ostate f n.
  Proof.
    intros H1 H2. specialize (H1 n). cbv [step_ostate stuck_ostate] in H1.
    destruct (f n) as [st|] eqn:Est; [|destruct H2]. destruct H1 as [H1|[H1|H1]].
    - destruct (f (S n)) as [st'|]; [|destruct H1]. exfalso. apply H2.
      eexists. apply H1.
    - cbv [stuck_ostate]. rewrite Est. assumption.
    - fwd. congruence.
  Qed.

  Lemma stuck_stable f n :
    possible_execution f ->
    o1 state_stuck (f n) ->
    forall m, n < m ->
              f m = None.
  Proof.
    intros H1 H2 m Hm. apply (state_stuck_stuck_state _ _ H1) in H2. destruct H2.
    eapply done_stable; eassumption.
  Qed.    

  Lemma possible_execution_offset f k :
    possible_execution f ->
    possible_execution (fun i => f (k + i)).
  Proof.
    cbv [possible_execution step_ostate stuck_ostate]. intros. specialize (H (k + i)).
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
    intros H1 [i H2]. cbv [satisfies]. exists i. destruct (f i) as [st|]; [|destruct H2].
    destruct H2.
    - destr_sstate st. left. intuition.
    - right. assumption.
  Qed.

  Lemma execution_of_first_part_stable' f n :
    option_map get_scmd (execution_of_first_part f n) = Some sskip ->
    forall m, n < m ->
              execution_of_first_part f m = None.
  Proof.
    intros. replace m with ((m - n - 1) + S n) by lia. clear H0.
    destruct (execution_of_first_part f n) as [ffn|] eqn:Effn; [|discriminate H].
    destr_sstate ffn. simpl in H. inversion H. clear H. subst. induction (m - n - 1).
    - simpl. rewrite Effn. reflexivity.
    - simpl. rewrite IHn0. reflexivity.
  Qed.

  Lemma first_part_1 f i :
    execution_of_first_part f i <> None ->
    execution_of_first_part f i = first_part (f i).
  Proof.
    intros H. destruct i.
    - reflexivity.
    - simpl in *. destruct (execution_of_first_part f i) as [st|]; [|congruence].
      destr_sstate st. destruct s; try reflexivity. congruence.
  Qed.

  Definition append s' (st : sstate) :=
    let '(s, k, t, m, l, mc) := st in (sseq s s', k, t, m, l, mc).

  Lemma second_comes_after_first s1 s2 k t m l mc k' t' m' l' mc' f i :
    f O = Some (sseq s1 s2, k, t, m, l, mc) ->
    possible_execution f ->
    execution_of_first_part f i = Some (sskip, k', t', m', l', mc') ->
    f (S i) = Some (s2, k', t', m', l', mc').
  Proof.
    intros H1 H2 H3.
    assert (forall n, n <= i -> f n = option_map (append s2) (execution_of_first_part f n)). (*this deserves to be its own lemma*)
    { intros n. induction n.
      - intros. simpl. rewrite H1. reflexivity.
      - intros H. specialize (IHn ltac:(lia)). assert (Hn := H2 n). destruct Hn as [Hn|[Hn|Hn]].
        + simpl. destruct (execution_of_first_part f n) as [st|] eqn:E1.
          2: { simpl in IHn. eapply done_stable; eassumption || lia. }
          destr_sstate st. simpl in IHn. cbv [step_ostate] in Hn. rewrite IHn in Hn.
          destruct (f (S n)) as [st'|]; simpl in Hn; [|destruct Hn]. destr_sstate st'.
          inversion Hn; subst.
          -- inversion H16; reflexivity.
          -- exfalso. assert (H' := execution_of_first_part_stable').
             specialize (H' f n). rewrite E1 in H'. specialize (H' eq_refl i ltac:(lia)).
             rewrite H3 in H'. simpl in H'. discriminate H'.
        + destruct Hn.
          assert (Hdone := stuck_stable f n ltac:(assumption) ltac:(assumption) i ltac:(lia)).
          destruct i as [|i]; [lia|]. simpl in H3. rewrite Hdone in H3.
          destruct (execution_of_first_part f i) as [st|]; [|congruence].
          destr_sstate st. destruct s; simpl in H3; congruence.
        + fwd. simpl. rewrite Hnp1. destruct (execution_of_first_part f n) as [st|]; [|congruence].
          destr_sstate st. destruct s; reflexivity. }
    specialize (H i ltac:(lia)). rewrite H3 in H. simpl in H. specialize (H2 i).
    cbv [step_ostate stuck_ostate] in H2. destruct H2 as [H2|[H2|H2]].
    - rewrite H in H2. destruct (f (S i)) as [st'|]; [|destruct H2].
      destr_sstate st'. inversion H2; subst.
      + inversion H16.
      + reflexivity.
    - fwd. destruct (f i) as [st'|]; [|destruct H2p0]. inversion H; clear H; subst.
      exfalso. apply H2p0. eexists (_, _, _, _, _, _). eapply seq_done_step.
    - fwd. congruence.
  Qed.
  
  Lemma build_seq s1 s2 k t m l mc post :
    (forall (f : nat -> _),
        f O = Some (s1, k, t, m, l, mc) ->
        possible_execution f ->
        satisfies f (fun k' t' m' l' mc' =>
                       forall (g : nat -> _),
                         g O = Some (s2, k', t', m', l', mc') ->
                         possible_execution g ->
                         satisfies g post)) ->
    forall (f : nat -> _),
      f O = Some (sseq s1 s2, k, t, m, l, mc) ->
      possible_execution f ->
      satisfies f post.
  Proof.
    intros. specialize (H (execution_of_first_part f)).
    simpl in H. rewrite H0 in H. specialize (H eq_refl (possible_first_part _ H1)).
    destruct H as [i H]. destruct (execution_of_first_part f i) as [st|] eqn:E; [|destruct H].
    destruct H as [H | H].
    - destr_sstate st. destruct H. subst. assert (H3 := second_comes_after_first).
      specialize H3 with (1 := H0) (2 := H1) (3 := E).
      specialize (H2 (fun j => f (S i + j))).
      simpl in H2. replace (i + 0) with i in H2 by lia.
      replace (fun j => f (S (i + j))) with (fun j => f (S i + j)) in H2 by reflexivity.
      specialize (H2 H3 (possible_execution_offset _ _ H1)).
      eapply satisfies_offset. eapply H2.
    - rewrite first_part_1 in E. 2: congruence.
      cbv [satisfies]. exists i. destruct (f i) as [st_s2|] eqn:E'; [|simpl in E; congruence].
      simpl. cbv [state_satisfies]. right. destr_sstate st_s2.
      destruct s; simpl in E; try congruence. inversion E; clear E; subst. inversion H; subst.
      + constructor. constructor; assumption.
      + econstructor; eassumption.
      + econstructor; eassumption.
      + econstructor; eassumption.
  Qed.

  Definition execute_with_tail (f : nat -> option sstate) (s2 : scmd) (n : nat) : option sstate :=
    match f n with
    | Some (s, k, t, m, l, mc) => Some (sseq s s2, k, t, m, l, mc)
    | None => None
    end.

  (*Lemma simple_execute_with_tail f s2 n :
    f n <> None ->
    execute_with_tail f s2 n =
      let '(s, k, t, m, l, mc) := f n in Some (sseq s s2, k, t, m, l, mc).
  Proof.
    intros H. cbv [execute_with_tail]. destr_sstate (f n).
    destruct s; try reflexivity. simpl in H. congruence.
  Qed.*)

  Lemma step_until_stuck f n :
    possible_execution f ->
    f n <> None ->
    forall m, m < n -> step_ostate f m.
  Proof.
    intros H1 H2. intros. assert (Hm := H1 m). destruct Hm as [Hm|Hm]; [assumption|].
    exfalso. apply H2. destruct Hm as [Hm|Hm].
    - destruct Hm. eapply stuck_stable; eassumption.
    - fwd. eapply done_stable; eassumption.
  Qed.

  Fixpoint repeat_f {A: Type} (f : A -> A) x n :=
    match n with
    | O => x
    | S n' => f (repeat_f f x n')
    end.

  Lemma possible_execution_exists st :
    exists f, f O = st /\ possible_execution f.
  Proof.
    cbv [possible_execution step_ostate stuck_ostate].
    assert (Hnext : exists (next : option sstate -> option sstate), forall st,
               o2 state_step st (next st) \/ o1 state_stuck st /\ next st = None \/ st = None /\ next st = None).
    { clear -choice em. cbv [FunctionalChoice_on] in choice.
      apply (choice (fun st st' => o2 state_step st st' \/ o1 state_stuck st /\ st' = None \/ st = None /\ st' = None)).
      intros st. assert (step_or_not := em (exists st', o2 state_step st st')).
      destruct step_or_not as [step|not].
      - destruct step as [st' step]. exists st'. left. assumption.
      - exists None. right. destruct st as [st|]; auto. left. split; [|reflexivity].
        destr_sstate st. cbv [state_stuck]. intros [st' H']. apply not. eexists (Some _).
        eassumption. }
    destruct Hnext as [next Hnext]. Print repeat_f.
    exists (fun n => repeat_f next st n). split; [reflexivity|]. intros.
    apply Hnext.
  Qed.

  Lemma later_comes_after f i j :
    possible_execution f ->
    step_ostate f i ->
    f j <> None ->
    i < j ->
    o2 comes_after (f j) (f i).
  Proof.
    intros H1 H2 H3. induction j.
    - lia.
    - destruct (Nat.ltb i j) eqn:E.
      + apply PeanoNat.Nat.ltb_lt in E. eassert (hyp : _). 2: specialize (IHj hyp); clear hyp.
        { intros H. apply H3. apply (done_stable _ j); try assumption; try lia. }
        intros H. specialize (IHj ltac:(lia)). specialize (H1 j).
        cbv [step_ostate stuck_ostate] in H1.
        destruct (f j) as [st'|] eqn:Ej, (f i) as [st|] eqn:Ei; try solve [destruct IHj].
        destruct (f (S j)) as [st''|] eqn:ESj; try congruence.
        destruct H1 as [H1|[H1|H1]].
        -- eapply t_trans. 2: eassumption. apply t_step. apply H1.
        -- destruct H1 as [_ H1]. exfalso. auto.
        -- fwd. congruence.
      + intros. apply PeanoNat.Nat.ltb_nlt in E. replace j with i by lia.
        cbv [step_ostate] in H2. destruct (f i), (f (S i)); try solve [destruct H2].
        apply t_step. apply H2.
  Qed.

  Lemma comes_after_seq' st st' s :
      comes_after st' st ->
      comes_after (append s st') (append s st).
  Proof.
    intros H. induction H.
    - apply t_step. destr_sstate x. destr_sstate y. apply seq_step. apply H.
    - eapply t_trans; eassumption.
  Qed.

  Lemma comes_after_seq s k t m l mc s' k' t' m' l' mc' s2 :
    comes_after (s', k', t', m', l', mc') (s, k, t, m, l, mc) ->
    comes_after (sseq s' s2, k', t', m', l', mc') (sseq s s2, k, t, m, l, mc).
  Proof. apply (comes_after_seq' (s, k, t, m, l, mc) (s', k', t', m', l', mc')). Qed.
    
  Lemma invert_seq s1 s2 k t m l mc post :
    (forall (f : nat -> _),
        f O = Some (sseq s1 s2, k, t, m, l, mc) ->
        possible_execution f ->
        satisfies f post) ->
    (forall (f : nat -> _),
        f O = Some (s1, k, t, m, l, mc) ->
        possible_execution f ->
        satisfies f (fun k' t' m' l' mc' =>
                       comes_after (s2, k', t', m', l', mc') (sseq s1 s2, k, t, m, l, mc) /\
                         forall (g : nat -> _),
                           g O = Some (s2, k', t', m', l', mc') ->
                           possible_execution g ->
                           satisfies g post)).
  Proof.
    intros H f HfO Hfposs.
    
(*is excluded middle really necessary here? intuitively it seems like the only option...
      yes, it is necessary.
      If I wanted to first define some execution f of sseq s1 s2 without first branching on whether
      the execution of (s1, k, t, m, l, mc) terminates, then I wouldn't know ahead of time what 
      would be the (sseq sskip s2, k', t', m', l', mc') state that the sseq s1 s2 eventually ends 
      up in, so I'd then need to have some map (s2, k', t', m', l', mc') |-> g, where g is a 
      possible_execution starting with that state.  Defining that map would use excluded middle 
      and choice, as in the proof of possible_execution_exists.*)
    assert (terminates_or_not := em (exists n, option_map get_scmd (f n) = Some sskip)).
    destruct terminates_or_not as [terminates|not].
    2: { assert (Hseqposs : possible_execution (execute_with_tail f s2)).
         { intros n. specialize (Hfposs n).
           cbv [step_ostate state_step stuck_ostate execute_with_tail] in *.
           destruct Hfposs as [Hfposs|[Hfposs|Hfposs]].
           - destruct (f n) as [st|] eqn:E, (f (S n)) as [st'|] eqn:E'; try solve [destruct Hfposs].
             destr_sstate st. destr_sstate st'.
             left. simpl. simpl in Hfposs. apply seq_step. assumption.
           - fwd. destruct (f n) as [st|] eqn:E; try solve [destruct Hfpossp0].
             destr_sstate st. right. left. split; [|reflexivity]. simpl.
             intros H'. fwd. apply Hfpossp0.
             destr_sstate st'. inversion H'; subst.
             + eexists (_, _, _, _, _, _). eassumption.
             + exfalso. apply not. exists n. rewrite E. reflexivity.
           - right. right. fwd. auto. }
         Fail specialize (H _ eq_refl Hseqposs). (*weird error message*)
         specialize (H (execute_with_tail f s2)). cbv [execute_with_tail] in H.
         rewrite HfO in H. specialize (H eq_refl Hseqposs). destruct H as [n H].
         exists n. destruct (f n) as [st|]; [|destruct H]. right. destr_sstate st.
         destruct H as [H|H].
         { destruct H as [H _]. discriminate H. }
         inversion H. subst. assumption. }
    destruct terminates as [n terminates]. exists n.
    destruct (f n) as [st|] eqn:E; [|simpl in terminates; congruence]. destr_sstate st.
    simpl in terminates. subst. inversion terminates; clear terminates; subst.
    assert (Hs1 := step_until_stuck f n Hfposs ltac:(congruence)).
    simpl. cbv [state_satisfies].
    left. split; [reflexivity|]. split.
    { enough (H' : o2 comes_after (f n) (Some (s1, k, t, m, l, mc)) \/ f n = Some (s1, k, t, m, l, mc)).
      { rewrite E in H'. destruct H' as [H'|H'].
        - eapply t_trans.
          2: { apply comes_after_seq. apply H'. }
          apply t_step. apply seq_done_step.
        - inversion H'. subst. apply t_step. apply seq_done_step. }
      rewrite <- HfO. clear -Hs1. induction n.
      - right. reflexivity.
      - left. eassert (hyp : _). 2: specialize (IHn hyp); clear hyp.
        { intros. apply Hs1. lia. }
        specialize (Hs1 n ltac:(lia)). cbv [step_ostate state_step execute_with_tail] in Hs1.
        destruct (f (S n)) as [st''|], (f n) as [st'|]; try solve [destruct Hs1].
        destruct IHn as [IHn|IHn].
        + destruct (f O) as [st|]; try solve [destruct IHn].
          simpl in Hs1. destr_sstate st'. eapply t_trans.
          -- apply t_step. instantiate (1 := (_, _, _, _, _, _)). eassumption.
          -- assumption.
        + destruct (f O) as [st|]; try congruence. inversion IHn; clear IHn; subst.
          apply t_step. assumption. }
    intros f2 Hf2O Hf2poss.
    remember (fun m =>
                if Nat.leb m n
                then execute_with_tail f s2 m
                else f2 (m - n - 1)) as g eqn:Eg.
    specialize (H g). eassert (HgO : g O = _).
    { rewrite Eg. simpl. cbv [execute_with_tail]. rewrite HfO. reflexivity. }
    specialize (H HgO). clear HgO. assert (Hgposs : possible_execution g).
    { intros i. specialize (Hs1 i).
      cbv [possible_execution] in Hf2poss. cbv [step_ostate state_step stuck_ostate] in *.
      subst. cbv [execute_with_tail] in *. destruct (Nat.leb i n) eqn:Ei.
      - apply PeanoNat.Nat.leb_le in Ei. destruct (Nat.leb (S i) n) eqn:ESi.
        + apply PeanoNat.Nat.leb_le in ESi. specialize (Hs1 ltac:(lia)).
          destruct (f i) as [st|]; [|destruct Hs1]. destruct (f (S i)) as [st'|]; [|destruct Hs1].
          destr_sstate st. destr_sstate st'. simpl. left. apply seq_step. assumption.
        + apply PeanoNat.Nat.leb_nle in ESi. assert (i = n) by lia. subst.
          left. rewrite E. replace (S n - n - 1) with O by lia.
          rewrite Hf2O. simpl. constructor.
      - apply PeanoNat.Nat.leb_nle in Ei. destruct (Nat.leb (S i) n) eqn:ESi.
        + apply PeanoNat.Nat.leb_le in ESi. lia.
        + apply PeanoNat.Nat.leb_nle in ESi. replace (S i - n - 1) with (S (i - n - 1)) by lia.
          apply Hf2poss. }
    specialize (H Hgposs). destruct H as [b H]. exists (b - n - 1).
    rewrite Eg in H. cbv [state_satisfies execute_with_tail] in H.
    destruct (Nat.leb b n) eqn:E1.
    { exfalso. apply PeanoNat.Nat.leb_le in E1.
      destruct (f b) as [stb|] eqn:Eb; [|destruct H]. destr_sstate stb. simpl in H.
      destruct H as [H|H].
      - destruct H as [H _]. discriminate H.
      - specialize (Hs1 b). destruct (Nat.eqb b n) eqn:E2.
        + apply PeanoNat.Nat.eqb_eq in E2. subst. rewrite Eb in E. inversion E. clear E. subst.
          inversion H. subst. inversion H1.
        + apply PeanoNat.Nat.eqb_neq in E2. specialize (Hs1 ltac:(lia)).
          cbv [step_ostate] in Hs1. subst. rewrite Eb in Hs1.
          destruct (f (S b)) as [st'|]; [|destruct Hs1]. simpl in Hs1. destr_sstate st'.
          apply good_stuck_stuck in H. apply H. eexists (_, _, _, _, _, _). eapply seq_step.
          eassumption. }
    apply H.
  Qed.

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
    exec s k t m l mc post ->
    forall (f : nat -> _),
      f O = Some (inclusion s, k, t, m, l, mc) ->
      possible_execution f ->
      satisfies f post.
  Proof.
    intros H. induction H.
    - intros. exists O. rewrite H0. left. eauto.
    - intros f HO HS. assert (HSO := HS O). destruct HSO as [HSO | [HSO | HSO] ].
      + exists (S O). cbv [step_ostate state_step] in HSO. rewrite HO in HSO.
        destruct (f (S O)) as [st'|]; [|destruct HSO]. destr_sstate st'.
        simpl in HSO. simpl. inversion HSO. subst. unify_eval_exprs. left. eauto.
      + exfalso. cbv [stuck_ostate] in HSO. rewrite HO in HSO. destruct HSO as [HSO _].
        apply HSO. eexists (_, _, _, _, _, _). econstructor; eassumption.
      + fwd. congruence.
    - intros f HO HS. assert (HSO := HS O). destruct HSO as [HSO | [HSO | HSO] ].
      + exists (S O). cbv [step_ostate state_step] in HSO. rewrite HO in HSO.
        destruct (f (S O)) as [st'|]; [|destruct HSO]. destr_sstate st'.
        simpl in HSO. simpl. inversion HSO. subst. unify_eval_exprs. left. eauto.
      + exfalso. cbv [stuck_ostate] in HSO. rewrite HO in HSO. destruct HSO as [HSO _].
        apply HSO. eexists (_, _, _, _, _, _). econstructor; eassumption.
      + fwd. congruence.
    - intros f HO HS. assert (HSO := HS O). destruct HSO as [HSO | [HSO | HSO] ].
      + exists (S O). cbv [step_ostate state_step] in HSO. rewrite HO in HSO.
        destruct (f (S O)) as [st'|]; [|destruct HSO]. destr_sstate st'.
        simpl in HSO. simpl. inversion HSO. subst. unify_eval_exprs. left. eauto.
      + exfalso. cbv [stuck_ostate] in HSO. rewrite HO in HSO. destruct HSO as [HSO _].
        apply HSO. eexists (_, _, _, _, _, _). econstructor; eassumption.
      + fwd. congruence.
    - intros f HO HS. simpl in HO. clear H0. assert (HSO := HS O).
      destruct HSO as [HSO | [HSO|HSO]].
      + cbv [step_ostate state_step] in HSO. rewrite HO in HSO.
        destruct (f (S O)) as [st'|] eqn:Est'; [|destruct HSO]. destr_sstate st'.
        simpl in HSO. inversion HSO. subst. clear HO.
        eapply satisfies_offset; eauto.
        instantiate (1 := S O). 
        eapply build_seq.
        2: apply Est'.
        2: apply possible_execution_offset; assumption.
        intros.
        eapply satisfies_weaken. 2: eapply H1; eauto.
        simpl. intros.
        specialize (H7 O). cbv [step_ostate stuck_ostate state_step] in H7.
        rewrite H6 in *. clear H6.
        repeat match goal with
               | H: anybytes _ _ _ |- _ => clear H
               | H: map.split _ _ _ |- _ => clear H
               end.
        destruct H7 as [H7 | [H7 | H7]].
        -- destruct (g (S O)) as [st'|] eqn:Eg1; [|destruct H7]. destr_sstate st'.
           inversion H7. subst. fwd.
           match goal with
           | A: map.split _ _ _, B: map.split _ _ _ |- _ =>
               specialize @map.split_diff with (4 := A) (5 := B) as P
           end.
           edestruct P; try typeclasses eauto.
           1: eapply anybytes_unique_domain; eassumption.
           subst. eexists (S O). rewrite Eg1. left. auto.
        -- exfalso. apply H7. clear H7. fwd. eexists (_, _, _, _, _, _).
           econstructor; eauto.
        -- fwd. congruence.
      + exists O. rewrite HO. right. econstructor; try eassumption.
        cbv [stuck_ostate] in HSO. rewrite HO in HSO. destruct HSO. assumption.
      + fwd. congruence.
    - intros f HO HS. assert (HSO := HS O). destruct HSO as [HSO | [HSO | HSO]].
      + cbv [step_ostate state_step] in HSO. rewrite HO in HSO.
        destruct (f (S O)) as [st'|] eqn:Est'; [|destruct HSO]. destr_sstate st'.
        inversion HSO; try congruence. subst. unify_eval_exprs.
        specialize (IHexec (fun i => f (1 + i))). simpl in IHexec. rewrite Est' in IHexec.
        specialize (IHexec eq_refl). assert (Hposs := possible_execution_offset _ 1%nat HS).
        specialize (IHexec Hposs). clear Hposs. Search satisfies.
        apply (satisfies_offset _ 1%nat) in IHexec; eauto.
      + cbv [stuck_ostate] in HSO. exfalso. destruct HSO as [HSO _]. rewrite HO in HSO.
        apply HSO. clear HSO. eexists (_, _, _, _, _, _). eapply if_true_step; eauto.
      + fwd. congruence.
    - intros f HO HS. assert (HSO := HS O). destruct HSO as [HSO | [HSO | HSO]].
      + cbv [step_ostate state_step] in HSO. rewrite HO in HSO.
        destruct (f (S O)) as [st'|] eqn:Est'; [|destruct HSO]. destr_sstate st'.
        inversion HSO; try congruence. subst. unify_eval_exprs.
        specialize (IHexec (fun i => f (1 + i))). simpl in IHexec. rewrite Est' in IHexec.
        specialize (IHexec eq_refl). assert (Hposs := possible_execution_offset _ 1%nat HS).
        specialize (IHexec Hposs). clear Hposs. Search satisfies.
        apply (satisfies_offset _ 1%nat) in IHexec; eauto.
      + cbv [stuck_ostate] in HSO. exfalso. destruct HSO as [HSO _]. rewrite HO in HSO.
        apply HSO. clear HSO. eexists (_, _, _, _, _, _). eapply if_false_step; eauto.
      + fwd. congruence.
    - eapply build_seq. fold inclusion. intros f H2 H3. eapply satisfies_weaken; eauto.
    - intros f HO HS. assert (HSO := HS O). destruct HSO as [HSO | [HSO | HSO] ].
      + cbv [step_ostate state_step] in HSO. rewrite HO in HSO.
        destruct (f (S O)) as [st'|] eqn:Est'; [|destruct HSO]. destr_sstate st'.
        inversion HSO; try congruence. subst. unify_eval_exprs. exists (S O). rewrite Est'.
        left. eauto.
      + exfalso. cbv [stuck_ostate] in HSO. destruct HSO as [HSO _]. rewrite HO in HSO.
        apply HSO. clear HSO. eexists (_, _, _, _, _, _). econstructor; eauto.
      + fwd. congruence.
    - intros f HO HS. assert (HSO := HS O). destruct HSO as [HSO | [HSO | HSO] ].
      + cbv [step_ostate state_step] in HSO. rewrite HO in HSO.
        destruct (f (S O)) as [st'|] eqn:Est'; [|destruct HSO]. destr_sstate st'.
        inversion HSO; try congruence. subst. unify_eval_exprs. eapply satisfies_offset; eauto.
        instantiate (1 := 1%nat). eapply build_seq; eauto.
        2: eapply possible_execution_offset; eauto.
        intros. eapply satisfies_weaken; eauto. intros * g ? HgO HgS.
        assert (HgSO := HgS O). destruct HgSO as [HgSO | [HgSO | HgSO] ].
        -- cbv [step_ostate state_step] in HgSO. rewrite HgO in HgSO.
           destruct (g0 (S O)) as [stg01|] eqn:Eg1; [|destruct HgSO]. destr_sstate stg01.
           inversion HgSO. subst. inversion H20. subst. assert (HgSSO := HgS (S O)).
           destruct HgSSO as [HgSSO | [HgSSO | HgSSO] ].
           ++ cbv [step_ostate state_step] in HgSSO. rewrite Eg1 in HgSSO.
              destruct (g0 2%nat) as [stg02|] eqn:Eg02; [|destruct HgSSO]. destr_sstate stg02.
              inversion HgSSO; subst.
              --- inversion H21.
              --- eapply satisfies_offset; eauto. instantiate (1 := 2%nat).
                  eapply H3; eauto. apply possible_execution_offset. assumption.
           ++ exfalso. cbv [stuck_ostate] in HgSSO. rewrite Eg1 in HgSSO. apply HgSSO.
              eexists (_, _, _, _, _, _). eapply seq_done_step.
           ++ fwd. congruence.
        -- exfalso. cbv [stuck_ostate] in HgSO. rewrite HgO in HgSO. destruct HgSO as [HgSO _].
           apply HgSO. eexists (_, _, _, _, _, _). eapply seq_step. econstructor.
        -- fwd. congruence.
      + exfalso. destruct HSO as [HSO _]. rewrite HO in HSO. apply HSO.
        eexists (_, _, _, _, _, _). eapply while_true_step; eauto.
      + fwd. congruence.
    - intros f HO HS. assert (HSO := HS O). destruct HSO as [HSO | [HSO | HSO] ].
      + cbv [step_ostate state_step] in HSO. rewrite HO in HSO.
        destruct (f (S O)) as [st'|] eqn:Est'; [|destruct HSO]. destr_sstate st'.
        inversion HSO. subst. unify_eval_exprs. eapply satisfies_offset.
        instantiate (1 := 1%nat). eapply build_seq; eauto.
        2: eapply possible_execution_offset; eauto.
        intros g HgO HgS. eapply satisfies_weaken.
        2: { assert (HgSO := HgS O). destruct HgSO as [HgSO | [HgSO | HgSO] ].
             - cbv [step_ostate state_step] in HgSO. rewrite HgO in HgSO.
               destruct (g (S O)) as [st'g|] eqn:Est'g; [|destruct HgSO]. destr_sstate st'g.
               inversion HgSO. subst. unify_eval_exprs. eapply satisfies_offset with (k := 1%nat).
               eapply IHexec; eauto. apply possible_execution_offset; auto.
             - exfalso. destruct HgSO as [HgSO _]. rewrite HgO in HgSO. apply HgSO.
               eexists (_, _, _, _, _, _). econstructor; eauto.
             - fwd. congruence. }
        intros * Hmid h HhO HhS. apply H3 in Hmid. fwd.
        assert (HhSO := HhS O). destruct HhSO as [HhSO | [HhSO | HhSO] ].
        -- cbv [step_ostate state_step] in HhSO. rewrite HhO in HhSO.
           destruct (h (S O)) as [st'h|] eqn:Est'h; [|destruct HhSO]. destr_sstate st'h.
           inversion HhSO. subst. fwd. unify_eval_exprs. exists (S O). rewrite Est'h. left. eauto.
        -- exfalso. destruct HhSO as [HhSO _]. rewrite HhO in HhSO. apply HhSO.
           eexists (_, _, _, _, _, _). econstructor; eauto.
        -- fwd. congruence.
      + exfalso. destruct HSO as [HSO _]. rewrite HO in HSO. apply HSO.
        eexists (_, _, _, _, _, _). econstructor; eauto.
      + fwd. congruence.
    - destruct ext_spec_ok.
      intros f HO HS. assert (HSO := HS O). destruct HSO as [HSO | [HSO | HSO] ].
      + cbv [step_ostate state_step] in HSO. rewrite HO in HSO.
        destruct (f (S O)) as [st'|] eqn:Est'; [|destruct HSO]. destr_sstate st'.
        inversion HSO. subst. unify_eval_exprs.
        specialize unique_mGive_footprint with (1 := H1) (2 := H19).
        destruct (map.split_diff unique_mGive_footprint H H6). subst.
        assert (HSSO := HS (S O)). destruct HSSO as [HSSO | [HSSO | HSSO] ].
        -- cbv [step_ostate state_step] in HSSO. rewrite Est' in HSSO.
           destruct (f (S (S O))) as [st''|] eqn:Est''; [|destruct HSSO]. destr_sstate st''.
           inversion HSSO. subst.
           exists (S (S O)). rewrite Est''. left. intuition.
           specialize H20 with (1 := H1). specialize H2 with (1 := H20). fwd.
           clear H unique_mGive_footprint.
           apply H2p1 in H26. unify_eval_exprs. apply H26.
        -- exists (S O). rewrite Est'. right. destruct HSSO as [HSSO _]. rewrite Est' in HSSO.
           econstructor.
           ++ apply H20 in H1. apply H2 in H1. fwd. eauto.
           ++ assumption.
        -- fwd. congruence.
      + assert (step_or_not :=
                  em (exists mReceive resvals klist,
                        (*(exists m', map.split m' mKeep mReceive)map.disjoint mKeep mReceive /\*)
                          forall mid',
                            ext_spec t mGive action args mid' ->
                            mid' mReceive resvals klist)).
        destruct step_or_not as [step | not_step].
        -- fwd. assert (Hmid := step _ H1). apply H2 in Hmid. fwd.
           exfalso. destruct HSO as [HSO _]. rewrite HO in HSO. apply HSO.
           eexists (_, _, _, _, _, _). econstructor; eauto.
           eapply weaken; eauto. cbv [pointwise_relation Basics.impl]. auto.
        -- exists O. rewrite HO. right. econstructor; eauto.
           { eapply weaken. 2: eassumption. cbv [pointwise_relation Basics.impl].
             intros * Hmid. apply H2 in Hmid. fwd. eauto. }
           intros H'. apply not_step. clear not_step. fwd. cbv [state_step step_ostate] in H'.
           destr_sstate st'. inversion H'. subst.
           unify_eval_exprs.
           specialize unique_mGive_footprint with (1 := H1) (2 := H19).
           destruct (map.split_diff unique_mGive_footprint H H6). subst.
           assert (Hmid := H20 _ H1).
           eexists. eexists. eexists. intuition eauto. eapply H20. apply H3.
      + fwd. congruence.
  Qed.

  Lemma enna (A : Type) (P : A -> Prop) :
    (forall y, P y) ->
    ~exists y, ~P y.
  Proof. intros H [y H']. apply H'. apply H. Qed.
  
  Lemma naen (A : Type) (P : A -> Prop) :
    ~(forall y, P y) ->
    exists y, ~P y.
  Proof.
    clear -em. cbv [excluded_middle]. intros H. assert (H1 := em (exists y, ~P y)).
    destruct H1 as [H1|H1].
    - assumption.
    - exfalso. apply H. clear H. intros y. assert (H2 := em (P y)).
      destruct H2 as [H2|H2].
      + assumption.
      + exfalso. apply H1. exists y. assumption.
  Qed.

  Lemma chains_finite_implies_Acc (A : Type) (R : A -> A -> Prop) x :
    FunctionalChoice_on A A ->
    (forall f : nat -> A,
        f O = x ->
        ~(forall i, R (f (S i)) (f i))) ->
    Acc R x.
  Proof.
    clear choice. intros choice H. cbv [FunctionalChoice_on] in choice.
    specialize (choice (fun x y => ~Acc R x -> ~Acc R y /\ R y x)). destruct choice as [f H'].
    { clear -em. intros x. cbv [excluded_middle] in em.
      assert (H1 := em (forall y : A, R y x -> Acc R y)). destruct H1 as [H1|H1].
      - exists x. intros H. exfalso. apply H. constructor. assumption.
      - assert (H2 := naen). specialize H2 with (1 := H1).
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

  Check Acc_union. Print inclusion.

  Lemma they_commute : commut _ prefix comes_right_after.
  Proof.
    cbv [commut]. intros. inversion H. subst. clear H. destr_sstate z.
    exists (sseq s s2, k0, t0, m0, l0, mc0).
    - cbv [comes_right_after state_step]. Print step. apply seq_step. apply H0.
    - constructor.
  Qed.

  Lemma clos_trans_l_commut {A : Type} (R1 R2 : relation A) :
    commut _ R1 R2 -> commut _ (clos_trans _ R1) R2.
  Proof.
    intros H. intros x y H1. induction H1.
    - intros z Hzx.
      specialize (H _ _ ltac:(eassumption) _ ltac:(eassumption)).
      destruct H as [x' H1' H2']. clear H0 Hzx x. exists x'.
      + assumption.
      + apply t_step. assumption.
    - Search x. intros z' H2. specialize IHclos_trans1 with (1 := H2).
      destruct IHclos_trans1. specialize IHclos_trans2 with (1 := H0).
      destruct IHclos_trans2. eexists; [eassumption|]. eapply t_trans; eassumption.
  Qed.

  Lemma clos_trans_r_commut {A : Type} (R1 R2 : relation A) :
    commut _ R1 R2 -> commut _ R1 (clos_trans _ R2).
  Proof.
    intros H. intros x y H1 z H2. revert x H1. induction H2.
    - intros z Hyz.
      specialize (H _ _ ltac:(eassumption) _ ltac:(eassumption)).
      destruct H as [y' H1' H2']. clear H0 Hyz y. exists y'.
      + apply t_step. assumption.
      + assumption.
    - intros z' H2. specialize IHclos_trans2 with (1 := H2).
      destruct IHclos_trans2. specialize IHclos_trans1 with (1 := H1).
      destruct IHclos_trans1. eexists; [|eassumption]. eapply t_trans; eassumption.
  Qed.

  Lemma clos_trans_commut {A : Type} (R1 R2 : relation A) :
    commut _ R1 R2 -> commut _ (clos_trans _ R1) (clos_trans _ R2).
  Proof. intros. apply clos_trans_l_commut. apply clos_trans_r_commut. assumption. Qed.         

  Lemma prefix_wf :
    well_founded prefix.
  Proof.
    cbv [well_founded]. intros. destr_sstate a. subst. revert k t m l mc. induction s.
    all: constructor; intros ? H; inversion H.
    subst. auto.
  Qed.

  Lemma lifted_Acc {A B : Type} (f : A -> B) R x :
    Acc R (f x) ->
    Acc (lift R f) x.
  Proof.
    intros. remember (f x) eqn:E. revert x E. induction H. intros. subst.
    constructor. intros. eapply H0.
    - eapply H1.
    - reflexivity.
  Qed.
  
  Lemma steps_Acc'' s k t m l mc post :
    (forall (f : nat -> option (scmd * _ * _ * _ * _ * _)),
        f O = Some (inclusion s, k, t, m, l, mc) ->
        possible_execution f ->
        satisfies f post) ->
    Acc comes_right_after (inclusion s, k, t, m, l, mc).
  Proof.
    intros. enough (Acc (lift (o2 comes_right_after) Some) (inclusion s, k, t, m, l, mc)).
    { apply H0. }
    apply lifted_Acc.
    apply chains_finite_implies_Acc; [apply choice|].
    clear em choice.
    intros. intros H'. specialize (H f).
    simpl in H. specialize (H H0).
    assert (possible_execution f).
    { cbv [possible_execution]. intros. left. cbv [step_ostate]. specialize (H' i).
      destruct (f i), (f (S i)); apply H'. (*that's kinda silly*) }
    apply H in H1.
    destruct H1 as [i H1]. specialize (H' i).
    destruct (f i) as [st|] eqn:Est; [|destruct H1]. destr_sstate st.
    destruct (f (S i)) as [st'|] eqn:Est'; [|destruct H']. destr_sstate st'.
    simpl in H1. simpl in H'. destruct H1 as [H1 | H1].
    - destruct H1 as [H1p1 H1p2]. subst. inversion H'.
    - assert (H'' : let '(s, k, t, m, l, mc) := st in
                    exists s' k' t' m' l' mc',
                      step s k t m l mc s' k' t' m' l' mc').
      { subst. do 6 eexists. eassumption. }
      rewrite <- Ef in *. clear Ef Est H'. induction H1.
      + apply H2. clear H2. fwd. eexists (_, _, _, _, _, _). eassumption.
      + apply H4. clear H4. fwd. eexists (_, _, _, _, _, _). eassumption.
      + apply H2. clear H2. fwd. eexists (_, _, _, _, _, _). eassumption.
      + apply IHgood_stuck. clear IHgood_stuck. fwd. inversion H''; subst.
        -- do 6 eexists. eassumption.
        -- inversion H1.
  Qed.

  Lemma steps_Acc' s k t m l mc post :
    (forall (f : nat -> option (scmd * _ * _ * _ * _ * _)),
        f O = Some (inclusion s, k, t, m, l, mc) ->
        possible_execution f ->
        satisfies f post) ->
    Acc comes_after_or_repeated_prefix (inclusion s, k, t, m, l, mc).
  Proof.
    intros. apply Acc_clos_trans. apply Acc_union.
    - apply clos_trans_commut. apply they_commute.
    - intros. apply Acc_clos_trans. apply prefix_wf.
    - apply Acc_clos_trans. eapply steps_Acc''; eassumption.
  Qed.

  Lemma steps_Acc s k t m l mc post :
    (forall (f : nat -> option (scmd * _ * _ * _ * _ * _)),
        f O = Some (inclusion s, k, t, m, l, mc) ->
        possible_execution f ->
        satisfies f post) ->
    Acc lifted_comes_after_or_repeated_prefix (s, k, t, m, l, mc).
  Proof.
    intros. apply lifted_Acc. eapply steps_Acc'; eassumption.
  Qed.

  Definition successful_execution f post :=
    forall i, step_ostate f i \/ o1 (state_satisfies post) (f i) \/ f i = None /\ f (S i) = None.

  (*it is such a pain that some of these things are stated
    in terms of option types and some are not. I should be consistent.*)
  Lemma stuck_unique f i j :
    possible_execution f ->
    o1 state_stuck (f i) ->
    o1 state_stuck (f j) ->
    i = j.
  Proof.
    intros H1 H2 H3. destruct (f i) as [fi|] eqn:Efi; [|destruct H2].
    destruct (f j) as [fj|] eqn:Efj; [|destruct H3].
    assert (~(i < j)).
    { intros Hlt. enough (f j = None) by congruence. eapply stuck_stable; try eassumption.
      rewrite Efi. eassumption. }
    assert (~ j < i).
    { intros Hlt. enough (f i = None) by congruence. eapply stuck_stable; try eassumption.
      rewrite Efj. eassumption. }
    lia.
  Qed.

  (*TODO (to make my proofs less long and repetitive): write a lemma that says
    satisfies f post -> forall i, get_scmd (f i) = sskip -> post (f i).*)

  Lemma stuck_satisfies f post :
    possible_execution f ->
    satisfies f post ->
    forall i,
      o1 state_stuck (f i) ->
      o1 (state_satisfies post) (f i).
  Proof.
    intros H1 H2 i H3. destruct H2 as [j H2]. destruct (f i) as [st|] eqn:Ei; [|destruct H3].
    destr_sstate st. destruct (f j) as [st_|] eqn:Ej; [|destruct H2].
    specialize satisfies_stuck with (1 := H2). intros H4. simpl in H3.
    specialize stuck_unique with (1 := H1). intros unique. specialize (unique i j).
    rewrite Ei, Ej in unique. specialize (unique ltac:(assumption) ltac:(assumption)). subst.
    rewrite Ei in Ej. inversion Ej. subst. simpl in H2. apply H2.
  Qed.

  Lemma satisfies_short f post i k t m l mc :
    possible_execution f ->
    satisfies f post ->
    f i = Some (sskip, k, t, m, l, mc) ->
    post k t m l mc.
  Proof.
    intros H1 H2 H3. enough (Hsati : o1 (state_satisfies post) (f i)).
    { rewrite H3 in Hsati. destruct Hsati as [Hsati|Hsati].
      - fwd. assumption.
      - inversion Hsati. }
    apply stuck_satisfies; try assumption. rewrite H3.
    intros [st' H']. destr_sstate st'. inversion H'.
  Qed.

  Lemma satisfies_stuck_good f i post : 
    possible_execution f ->
    satisfies f post ->
    o1 state_stuck (f i) ->
    o1 good_stuck (f i) \/ option_map get_scmd (f i) = Some sskip.
  Proof.
    intros H1 H2 H3. destruct H2 as [j H2]. destruct (f j) as [sj|] eqn:Ej; [|destruct H2].
    assert (i = j).
    { eapply stuck_unique; try eassumption. rewrite Ej. eapply satisfies_stuck; eassumption. }
    subst. rewrite Ej in *. destruct H2 as [H2|H2].
    - right. destr_sstate sj. fwd. reflexivity.
    - left. assumption.
  Qed.
  
  (*Lemma ps_suc f post :
    possible_execution f -> satisfies f post -> successful_execution f post.
  Proof.
    intros H1 H2 n. assert (H5 := H1 n). destruct H2 as [m H2]. destruct H5 as [H5|[H5|H5]].
    - left. assumption.
    - right. left. destruct (f m) as [fm|] eqn:Efm; [|destruct H2].
      destruct H5 as [H3 H4]. destruct (f n) as [fn|] eqn:Efn; [|destruct H3].
      specialize satisfies_stuck with (1 := H2). intros H6.
      specialize stuck_unique with (1 := H1). intros H7. specialize (H7 m n).
      rewrite Efm, Efn in H7. specialize H7 with (1 := H6) (2 := H3). subst.
      rewrite Efm in Efn. inversion Efn. subst. assumption.
    - right. right. assumption.
  Qed.*)

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
  
  Lemma step_to_exec s k t m l mc post :
    (forall (f : nat -> _),
        f O = Some (inclusion s, k, t, m, l, mc) ->
        possible_execution f ->
        satisfies f post) ->
    exec s k t m l mc post.
  Proof.
    intros H. assert (H' := steps_Acc).
    specialize H' with (1 := H).
    revert H. revert post.
    eapply (@Fix_F _ _ (fun x => let '(_, _, _, _, _, _) := x in _) _ _ H').
    Unshelve. simpl. clear -em choice word_ok mem_ok ext_spec_ok. intros. destr_sstate x. subst.
    intros post Hsat.
    (* there is a possible execution *)
    assert (Hposs := possible_execution_exists (Some (inclusion s, k, t, m, l, mc))).
    destruct Hposs as [f [HfO Hposs] ].
    assert (Hsatf := Hsat f HfO Hposs).
    destruct s.
    - econstructor. eapply satisfies_short; eauto.
    - assert (HpossO := Hposs O). destruct HpossO as [HpossO|[HpossO|HpossO]].
      + cbv [step_ostate] in HpossO. rewrite HfO in HpossO.
        destruct (f (S O)) as [st'|] eqn:Est'; [|destruct HpossO]. destr_sstate st'.
        inversion HpossO. subst. econstructor; try eassumption.
        eapply satisfies_short; eauto.
      + enough (sg : o1 good_stuck (f O) \/ option_map get_scmd (f O) = Some sskip).
        { rewrite HfO in sg. simpl in sg. destruct sg as [sg|sg]; [inversion sg|congruence]. }
        destruct HpossO. eapply satisfies_stuck_good; eassumption.
      + fwd. congruence.
    - assert (HpossO := Hposs O). destruct HpossO as [HpossO|[HpossO|HpossO]].
      + cbv [step_ostate] in HpossO. rewrite HfO in HpossO.
        destruct (f (S O)) as [st'|] eqn:Est'; [|destruct HpossO]. destr_sstate st'.
        inversion HpossO. subst. econstructor; try eassumption.
        eapply satisfies_short; eauto.
      + enough (sg : o1 good_stuck (f O) \/ option_map get_scmd (f O) = Some sskip).
        { rewrite HfO in sg. simpl in sg. destruct sg as [sg|sg]; [inversion sg|congruence]. }
        destruct HpossO. eapply satisfies_stuck_good; eassumption.
      + fwd. congruence.
    - assert (HpossO := Hposs O). destruct HpossO as [HpossO|[HpossO|HpossO]].
      + cbv [step_ostate] in HpossO. rewrite HfO in HpossO.
        destruct (f (S O)) as [st'|] eqn:Est'; [|destruct HpossO]. destr_sstate st'.
        inversion HpossO. subst. econstructor; try eassumption.
        eapply satisfies_short; eauto.
      + enough (sg : o1 good_stuck (f O) \/ option_map get_scmd (f O) = Some sskip).
        { rewrite HfO in sg. simpl in sg. destruct sg as [sg|sg]; [inversion sg|congruence]. }
        destruct HpossO. eapply satisfies_stuck_good; eassumption.
      + fwd. congruence.
    - assert (HpossO := Hposs O). destruct HpossO as [HpossO|[HpossO|HpossO]].
      2: { cbv [stuck_ostate] in HpossO. destruct HpossO as [HpossO _].
           eapply satisfies_stuck_good in HpossO; try eassumption. rewrite HfO in HpossO.
           simpl in HpossO. destruct HpossO as [HpossO|HpossO]; [|congruence].
           inversion HpossO. subst. econstructor; eauto. intros. exfalso. apply H8.
           eexists (_, _, _, _, _, _). econstructor; eauto. }
      2: { fwd. congruence. }
      cbv [step_ostate state_step] in HpossO. rewrite HfO in HpossO.
      destruct (f (S O)) as [st'|]; [|destruct HpossO]. destr_sstate st'.
      inversion HpossO. subst.
      econstructor; eauto. clear a f mStack HfO Hposs Hsatf Hposs HpossO H3 H15 H16.
      intros. eset (st2 := (_, _, _, _, _, _)).
      assert (Xs := X st2).
      eassert (lt : _). 2: specialize (Xs lt); clear lt.
      { cbv [lifted_comes_after_or_repeated_prefix lift]. simpl. eapply t_trans.
        2: { apply t_step. right. instantiate (1 := (_, _, _, _, _, _)).
             apply t_step. econstructor; eauto. }
        apply t_step. left. apply t_step. constructor. }
      simpl in Xs.
      eassert (Hind' : forall g, g O = Some (_, _, _, _, _, _) -> possible_execution g -> satisfies g post).
      { intros g HgO Hpossg. eset (Sg := fun n => match n with
                                                        | O => _
                                                        | S n' => g n'
                                                  end).
        specialize (Hsat Sg eq_refl). assert (Hsathyp : possible_execution Sg).
        2: specialize (Hsat Hsathyp); clear Hsathyp.
        { intros n. destruct n as [|n].
          - left. cbv [step_ostate state_step]. simpl. rewrite HgO. simpl.
            econstructor; eassumption.
          - apply Hpossg. }
        destruct Hsat as [i Hsat]. destruct i as [|i].
        { simpl in Hsat. destruct Hsat as [Hsat|Hsat].
          - destruct Hsat as [Hsat _]. congruence.
          - inversion Hsat. subst. exfalso. apply H12. clear H12.
            eexists (_, _, _, _, _, _). econstructor; eassumption. }
        exists i. apply Hsat. }
      assert (Hind := invert_seq). specialize Hind with (1 := Hind').
      specialize Xs with (1 := Hind). intros. eapply weaken. 1: eapply Xs.
      simpl. intros * [Hlt Hsat'].
      eassert (Hpossg := possible_execution_exists). edestruct Hpossg as [g [HgO Hpossg']].
      clear Hpossg. specialize Hsat' with (1 := HgO) (2 := Hpossg').
      assert (Hpossg'O := Hpossg' O). destruct Hpossg'O as [Hpossg'O|[Hpossg'O|Hpossg'O]].
      2: { cbv [stuck_ostate] in Hpossg'O. destruct Hpossg'O as [Hpossg'O _].
           eapply satisfies_stuck_good in Hpossg'O; try eassumption. rewrite HgO in Hpossg'O.
           simpl in Hpossg'O.
           destruct Hpossg'O as [Hpossg'O _|Hpossg'O]; [inversion Hpossg'O|congruence]. }
      2: { fwd. congruence. }
      cbv [step_ostate state_step] in Hpossg'O. rewrite HgO in Hpossg'O.
      destruct (g (S O)) as [st'|] eqn:Est'; [|destruct Hpossg'O]. destr_sstate st'.
      inversion Hpossg'O. subst. eexists. eexists. intuition eauto.
      eapply satisfies_short; eauto.
    - assert (HpossO := Hposs O). destruct HpossO as [HpossO|[HpossO|HpossO]].
      2: { destruct HpossO as [HpossO _]. eapply satisfies_stuck_good in HpossO; try eassumption.
           rewrite HfO in HpossO. simpl in HpossO. destruct HpossO as [HpossO|HpossO]; [inversion HpossO|congruence]. }
      2: { fwd. congruence. }
      cbv [step_ostate state_step] in HpossO. rewrite HfO in HpossO.
      destruct (f (S O)) as [st'|] eqn:Ef1; [|destruct HpossO]. destr_sstate st'.
      inversion HpossO; subst.
      + eassert (Xs1 := X _). eassert (lt : _). 2: specialize (Xs1 lt); clear lt.
        { cbv [lifted_comes_after_or_repeated_prefix lift].
          eapply t_step. right. eapply t_step.
          instantiate (1 := (_, _, _, _, _, _)). econstructor; eassumption. }
        simpl in Xs1. eapply if_true; try eassumption. eapply Xs1. clear Xs1.
        intros g HgO Hgposs. specialize (Hsat (fun n => match n with
                                                        | O => f O
                                                        | S n' => g n'
                                                        end)).
        simpl in Hsat. rewrite HfO in Hsat. specialize (Hsat eq_refl).
        eassert (Hsathyp : _). 2: specialize (Hsat Hsathyp); clear Hsathyp.
        { intros n. destruct n as [|n].
          - left. cbv [step_ostate state_step]. rewrite HgO. assumption.
          - specialize (Hgposs n). apply Hgposs. }
        destruct Hsat as [n Hsat]. destruct n as [|n].
        { destruct Hsat as [Hsat|Hsat].
          - destruct Hsat as [Hsat _]. simpl in Hsat. discriminate Hsat.
          - inversion Hsat. }
        exists n. apply Hsat.
      (*below, literally only changed if_true to if_false*)
      + eassert (Xs1 := X _). eassert (lt : _). 2: specialize (Xs1 lt); clear lt.
        { cbv [lifted_comes_after_or_repeated_prefix lift].
          eapply t_step. right. eapply t_step.
          instantiate (1 := (_, _, _, _, _, _)). econstructor; eassumption. }
        simpl in Xs1. eapply if_false; try eassumption. eapply Xs1. clear Xs1.
        intros g HgO Hgposs. specialize (Hsat (fun n => match n with
                                                        | O => f O
                                                        | S n' => g n'
                                                        end)).
        simpl in Hsat. rewrite HfO in Hsat. specialize (Hsat eq_refl).
        eassert (Hsathyp : _). 2: specialize (Hsat Hsathyp); clear Hsathyp.
        { intros n. destruct n as [|n].
          - left. cbv [step_ostate state_step]. rewrite HgO. assumption.
          - specialize (Hgposs n). apply Hgposs. }
        destruct Hsat as [n Hsat]. destruct n as [|n].
        { destruct Hsat as [Hsat|Hsat].
          - destruct Hsat as [Hsat _]. simpl in Hsat. discriminate Hsat.
          - inversion Hsat. }
        exists n. apply Hsat.
    - clear f HfO Hposs Hsatf.
      assert (Xs1 := X (s1, k, t, m, l, mc)). eassert (lt : _). 2: specialize (Xs1 lt); clear lt.
      { apply t_step. (* <- this is magic, and I do not understand it *)
        left. apply t_step. constructor. }
      simpl in Xs1. assert (Hsatinv := invert_seq). specialize Hsatinv with (1 := Hsat).
      fold inclusion in Hsatinv. specialize Xs1 with (1 := Hsatinv).
      econstructor. 1: eapply Xs1. simpl. intros * [afters2 Hs2].
      fold sstate in *.
      assert (Xs2 := X (s2, k', t', m', l', mc')). eassert (lt: _). 2: specialize (Xs2 lt); clear lt.
      { cbv [lifted_comes_after_or_repeated_prefix lift]. simpl.
        apply t_step. right. eassumption. }
      simpl in Xs2. specialize Xs2 with (1 := Hs2). apply Xs2.
    - assert (HpossO := Hposs O). destruct HpossO as [HpossO|[HpossO|HpossO]].
      2: { destruct HpossO as [HpossO _]. eapply satisfies_stuck_good in HpossO; try eassumption.
           rewrite HfO in HpossO. simpl in HpossO. destruct HpossO as [HpossO|HpossO]; [inversion HpossO|congruence]. }
      2: { fwd. congruence. }
      cbv [step_ostate state_step] in HpossO. rewrite HfO in HpossO.
      destruct (f (S O)) as [st'|] eqn:Ef1; [|destruct HpossO]. destr_sstate st'.
      inversion HpossO; subst.
      + eapply while_false; try eassumption. eapply satisfies_short; eassumption.
      + (*I'm kind of inlining the whole proof for the seq case here, plus some more stuff...
          I wouldn't have to do this if jump_back would just be a valid thing in the
          big-step language.  Arguably I should have some intermediate big-step language.
          Oh well. *)
        assert (forall g, g O = f (S O) -> possible_execution g -> satisfies g post).
        { intros. specialize (Hsat (fun n => match n with
                                             | O => f O
                                             | S n' => g n'
                                             end)).
          simpl in Hsat. rewrite HfO in Hsat. specialize (Hsat eq_refl).
          eassert (Hposs' : _). 2: specialize (Hsat Hposs'); clear Hposs'.
          { intros n. destruct n.
            - left. cbv [step_ostate state_step]. rewrite H. rewrite Ef1. apply HpossO.
            - apply H0. (*apply continues to impress and confuse me*) }
          destruct Hsat as [n Hsat]. destruct n as [|n].
          { cbv [state_satisfies] in Hsat. destruct Hsat as [Hsat|Hsat].
            - destruct Hsat as [Hsat _]. simpl in Hsat. congruence.
            - inversion Hsat. }
          exists n. apply Hsat. }
        rewrite Ef1 in H. assert (H' := invert_seq). specialize H' with (1 := H).
        clear H.
        assert (Xs := X (s, leak_bool true :: k', t0, m0, l0, mc0)).
        eassert (lt : _). 2: specialize (Xs lt); clear lt.
        { cbv [lifted_comes_after_or_repeated_prefix lift]. simpl. eapply t_trans.
          2: { apply t_step. right. apply t_step. cbv [comes_right_after state_step step_ostate].
               instantiate (1 := (_, _, _, _, _, _)). simpl. eassumption. }
          apply t_step. left. apply t_step. constructor. }
        simpl in Xs. specialize Xs with (1 := H'). clear H'.
        eapply while_true; try eassumption. simpl. intros * [Hlt Hind]. clear Xs.
        assert (Xw := X (cmd.while test s, k'', t', m', l', ami 2 (aml 2 (amj 1 mc'')))).
        eassert (lt' : _). 2: specialize (Xw lt'); clear lt'.
        { cbv [lifted_comes_after_or_repeated_prefix lift]. simpl.
          apply t_step. right. eapply t_trans.
          2: { apply t_step. instantiate (1 := (_, _, _, _, _, _)). apply HpossO. }
          eapply t_trans.
          2: { eassumption. }
          eapply t_trans.
          2: { apply t_step. instantiate (1 := (_, _, _, _, _, _)). eapply seq_step. econstructor. }
          eapply t_step. apply seq_done_step. }
        simpl in Xw. apply Xw.
        intros h HhO Hpossh. eset (h' := fun n => match n with
                                                  | O => _
                                                  | S O => _
                                                  | S (S n') => h n'
                                                  end).
        specialize (Hind h' eq_refl). assert (Hpossh' : possible_execution h').
        { intros n. destruct n as [|n].
          - left. cbv [step_ostate state_step]. simpl. instantiate (1 := Some (_, _, _, _, _, _)).
            simpl. eapply seq_step. econstructor.
          - destruct n as [|n].
            + left. cbv [step_ostate state_step]. simpl. rewrite HhO. constructor.
            + apply Hpossh. }
        specialize (Hind Hpossh'). clear Hpossh'. destruct Hind as [n Hind].
        destruct n as [|n].
        { cbv [state_satisfies] in Hind. simpl in Hind. destruct Hind as [Hind|Hind].
          - destruct Hind as [Hind _]. congruence.
          - inversion Hind. subst. inversion H0. }
        destruct n as [|n].
        { cbv [state_satisfies] in Hind. simpl in Hind. destruct Hind as [Hind|Hind].
          - destruct Hind as [Hind _]. congruence.
          - inversion Hind. subst. inversion H0. }
        cbv [satisfies]. exists n. apply Hind.
    - assert (HpossO := Hposs O). destruct HpossO as [HpossO|[HpossO|HpossO]].
      2: { destruct HpossO as [HpossO _]. eapply satisfies_stuck_good in HpossO; try eassumption.
           rewrite HfO in HpossO. simpl in HpossO. destruct HpossO as [HpossO|HpossO]; [inversion HpossO|congruence]. }
      2: { fwd. congruence. }
      cbv [step_ostate state_step] in HpossO. rewrite HfO in HpossO.
      destruct (f (S O)) as [f1|] eqn:Ef1; [|destruct HpossO]. destr_sstate f1.
      inversion HpossO. subst. assert (HpossSO := Hposs (S O)).
      destruct HpossSO as [HpossSO|[HpossSO|HpossSO]].
      2: { destruct HpossSO as [HpossSO _]. eapply satisfies_stuck_good in HpossSO; try eassumption.
           rewrite Ef1 in HpossSO. simpl in HpossSO. destruct HpossSO as [HpossSO|HpossSO]; [|congruence]. inversion HpossSO. subst. inversion H0. }
      2: { fwd. congruence. }
      cbv [step_ostate state_step] in HpossSO. rewrite Ef1 in HpossSO.
      destruct (f (S (S O))) as [f2|] eqn:Ef2; [|destruct HpossSO]. destr_sstate f2.
      inversion HpossSO. subst. inversion H12. subst.
      specialize (X (fbody, leak_unit :: k', t, m, l, ami 100 (amj 100 (aml 100 (ams 100 mc'))))).
      eassert (lt : _). 2: specialize (X lt); clear lt.
      { cbv [lifted_comes_after_or_repeated_prefix lift]. simpl. eapply t_trans.
        2: { apply t_step. right. eapply t_trans.
             2: { apply t_step. instantiate (1 := (_, _, _, _, _, _)). simpl. eassumption. }
             eapply t_step. instantiate (1 := (_, _, _, _, _, _)). simpl. eassumption. }
        apply t_step. left. apply t_step. constructor. }
      assert (Hind : forall g, g O = f (S (S O)) -> possible_execution g -> satisfies g post).
      { intros g HgO Hpossg. specialize (Hsat (fun n => match n with
                                                        | O => f O
                                                        | S O => f (S O)
                                                        | S (S n') => g n'
                                                        end)).
        simpl in Hsat. rewrite HfO in Hsat. specialize (Hsat eq_refl).
        eassert (Hposs' : _). 2: specialize (Hsat Hposs'); clear Hposs'.
        { intros n. destruct n as [|n].
          - left. cbv [step_ostate state_step]. rewrite Ef1. simpl. econstructor; eauto.
          - destruct n as [|n].
            + left. cbv [step_ostate state_step]. rewrite HgO, Ef1, Ef2. constructor.
              econstructor; eassumption.
            + apply Hpossg. }
        destruct Hsat as [n Hsat]. destruct n as [|n].
        { cbv [state_satisfies] in Hsat. simpl in Hsat. destruct Hsat as [Hsat|Hsat].
          - destruct Hsat as [Hsat _]. congruence.
          - inversion Hsat. }
        destruct n as [|n].
        { cbv [state_satisfies] in Hsat. rewrite Ef1 in Hsat. destruct Hsat as [Hsat|Hsat].
          - destruct Hsat as [Hsat _]. congruence.
          - inversion Hsat. subst. inversion H0. }
        exists n. apply Hsat. }
      rewrite Ef2 in Hind. assert (Hind' := invert_seq). specialize Hind' with (1 := Hind).
      clear Hind.
      simpl in X. specialize X with (1 := Hind'). clear Hind'.
      econstructor; try eassumption. (*X is one assumption*)
      simpl. intros * [Hlt Hafter].
      assert (Hposs' := possible_execution_exists (Some (end_call binds rets l0, k'', t', m', st1, mc''))).
      destruct Hposs' as [g [HgO Hgposs]].
      assert (Hsatg := Hafter g HgO Hgposs). assert (HgpossO := Hgposs O).
      destruct HgpossO as [HgpossO|[HgpossO|HgpossO]].
      2: { destruct HgpossO as [HgpossO _]. eapply satisfies_stuck_good in HgpossO; try eassumption.
           rewrite HgO in HgpossO. simpl in HgpossO. destruct HgpossO as [HgpossO|HgpossO]; [inversion HgpossO|congruence]. }
      2: { fwd. congruence. }
      cbv [step_ostate state_step] in HgpossO. rewrite HgO in HgpossO.
      destruct (g (S O)) as [g1|] eqn:Eg1; [|destruct HgpossO]. destr_sstate g1.
      inversion HgpossO. subst. fwd. eexists. intuition eauto. eexists. intuition eauto.
      eapply satisfies_short; eassumption.
    - destruct ext_spec_ok.
      assert (HpossO := Hposs O).
      assert (stuck_enough: o1 good_stuck (f O) -> exec (cmd.interact binds action args) k t m l mc post).
      { clear HpossO. intros Hstuck. rewrite HfO in Hstuck. inversion Hstuck. subst.
        econstructor. 3: eapply intersect. (*not H9*) all: try eassumption.
        simpl. intros * H. exfalso. apply H10. eexists (_, _, _, _, _, _).
        econstructor; eassumption. }
      destruct HpossO as [HpossO|[HpossO|HpossO]].
      2: { destruct HpossO as [HpossO _]. eapply satisfies_stuck_good in HpossO; try eassumption.
           rewrite HfO in HpossO. simpl in HpossO. destruct HpossO as [HpossO|HpossO]; [|congruence].
           apply stuck_enough. rewrite HfO. assumption. }
      2: { fwd. congruence. }
      cbv [step_ostate state_step] in HpossO. rewrite HfO in HpossO.
      destruct (f (S O)) as [f1|] eqn:Ef1; [|destruct HpossO]. destr_sstate f1.
      inversion HpossO. subst. econstructor. 3: eapply intersect. all: try eassumption.
      rewrite HfO in stuck_enough. simpl.
      clear f HfO Hposs Hsatf Hposs Ef1 mReceive resvals klist HpossO H16.
      intros * H. eset (f1 := (_, _, _, _, _, _)).
      assert (HpossSf := possible_execution_exists (Some f1)).
      destruct HpossSf as [Sf [SfO Sfposs]].
      eset (f := fun n => match n return option sstate with
                            | O => _
                            | S n' => Sf n'
                            end).
        specialize (Hsat f eq_refl). assert (Hpossf : possible_execution f).
      { intros n. destruct n.
        - left. cbv [step_ostate state_step]. simpl. rewrite SfO. econstructor; eassumption.
        - specialize (Sfposs n). apply Sfposs. }
      specialize (Hsat Hpossf).
      assert (Hdone := done_stable f (S (S O)) Hpossf). assert (HpossSO := Hpossf (S O)).
      destruct HpossSO as [HpossSO|[HpossSO|HpossSO]].
      2: { destruct HpossSO as [HpossSO _]. eapply satisfies_stuck_good in HpossSO; try eassumption.
           simpl in HpossSO. rewrite SfO in HpossSO. simpl in HpossSO.
           destruct HpossSO as [HpossSO|HpossSO]; [|congruence]. inversion HpossSO. subst.
           fwd. eexists. split; eauto. intros.
           exfalso. apply H17. clear H17. eexists (_, _, _, _, _, _). econstructor; eassumption. }
      2: { fwd. simpl in HpossSOp0. rewrite SfO in HpossSOp0. congruence. }
      cbv [step_ostate state_step] in HpossSO. simpl in HpossSO. rewrite SfO in HpossSO.
      destruct (Sf (S O)) as [Sf1|] eqn:ESf1; [|destruct HpossSO]. destr_sstate Sf1.
      inversion HpossSO. subst. eexists. split; eauto. intros.
      specialize @map.split_det with (1 := H23) (2 := H0).
      intros. subst. eapply satisfies_short; eauto.
      instantiate (1 := (S _)). simpl. eassumption.
  Qed.

  (*how far is it, in the worst case, from adding something to the trace*) Print scmd.
  Fixpoint size (s : scmd) :=
    match s with
    | sseq s1 s2 => S (size s1 + size s2)
    | sskip => O
    | scall _ _ _ => S (S (S (S (S O))))
    | start_call _ _ _ _ _ => S (S O)
    | sinteract _ _ _ => S (S O)
    | _ => S O
    end.

  Definition get_trace (st : sstate) :=
    let '(s, k, t, m, l, mc) := st in k.

  Lemma step_decreases_size_or_lengthens_trace st st' :
    state_step st st' ->
    length (get_trace st) < length (get_trace st') \/ length (get_trace st) <= length (get_trace st') /\ size (get_scmd st') < size (get_scmd st).
  Proof.
    intros H. destr_sstate st. destr_sstate st'. subst. induction H; subst_exprs.
    all: simpl in *; repeat rewrite app_length; lia.
  Qed.

  Definition val_def {A : Type} (default : A) (x : option A) :=
    match x with
    | Some x => x
    | None => default
    end.

  Definition oget_trace (ost : option sstate) :=
    match ost with
    | Some st => get_trace st
    | None => nil
    end.

  Definition oget_scmd (ost : option sstate) :=
    match ost with
    | Some st => get_scmd st
    | None => sskip
    end.

  Lemma steps_decrease_size_or_lengthen_trace (f : nat -> option sstate) n m :
    possible_execution f ->
    length (oget_trace (f n)) < length (oget_trace (f (m + n))) \/
      length (oget_trace (f n)) <= length (oget_trace (f (m + n))) /\
        size (oget_scmd (f (m + n))) + m <= size (oget_scmd (f n)) \/
      f (m + n) = None.
  Proof.
    intros H. induction m.
    - simpl. lia.
    - simpl. specialize (H (m + n)). destruct H as [H|[H|H]].
      + cbv [step_ostate] in H. destruct (f (m + n)), (f (S (m + n))); try solve [destruct H].
        apply step_decreases_size_or_lengthens_trace in H. simpl in *.
        destruct IHm as [IHm|[IHm|IHm]]; try lia. congruence.
      + destruct H as [_ H]. auto.
      + destruct H as [_ H]. auto.
  Qed.

  Lemma trace_lengthens (f : nat -> option sstate) n :
    possible_execution f ->
    length (oget_trace (f n)) < length (oget_trace (f (S (size (oget_scmd (f n))) + n))) \/
      f (S (size (oget_scmd (f n))) + n) = None.
  Proof.
    intros H. specialize (steps_decrease_size_or_lengthen_trace _ n (S (size (oget_scmd (f n)))) H).
    intros H'. destruct H' as [H'|[H'|H']]; try lia. auto.
  Qed.

  (*goes far enough to add length n to the trace*)
  Fixpoint enough_distance (f : nat -> option sstate) (distance : nat) (n : nat) :=
    match n with
    | O => distance
    | S n' => enough_distance f (S (size (oget_scmd (f distance))) + distance) n'
    end.

  Lemma its_enough' f d n :
    possible_execution f ->
    d <= enough_distance f d n /\
      (f (enough_distance f d n) = None \/ 
         n + length (oget_trace (f d)) <= length (oget_trace (f (enough_distance f d n)))).
  Proof.
    intros H. revert d. induction n.
    - intros. simpl. lia.
    - intros. simpl. specialize (IHn (S (size (oget_scmd (f d)) + d))). destruct IHn as [grow IHn].
      split; [lia|]. destruct IHn as [IHn|IHn].
      + left. assumption.
      + assert (longer:= trace_lengthens f d H). destruct longer as [longer|longer].
        2: { left. eapply done_stable; try eassumption. }
        right. simpl in *. lia.
  Qed.

  Lemma its_enough f d n :
    possible_execution f ->
    (f (enough_distance f d n) = None \/ 
       n + length (oget_trace (f d)) <= length (oget_trace (f (enough_distance f d n)))).
  Proof. intros H. eapply its_enough' in H. fwd. eauto. Qed.

  Search predicts.

  (*returns the index of a long enough trace*)
  Fixpoint get_long_trace (f : nat -> option sstate) fuel :=
    match fuel with
    | O => O
    | S fuel' =>
        match (f fuel) with
        | Some st => fuel
        | None => get_long_trace f fuel'
        end
    end. Print prefix.

  Lemma step_extends_trace st st' :
    state_step st st' ->
    exists k'', get_trace st' = k'' ++ get_trace st.
  Proof.
    intros H. destr_sstate st. destr_sstate st'. subst. induction H; subst_exprs.
    all: try (eexists; simpl; solve [trace_alignment]). fwd. exists k''. assumption.
  Qed.

  Lemma ostep_extends_trace st st' :
    o2 state_step st st' ->
    exists k'', oget_trace st' = k'' ++ oget_trace st.
  Proof.
    intros H. destruct st, st'; try solve [destruct H]. apply step_extends_trace. assumption.
  Qed.

  (*should prove this as a corollary of the thing above, or get rid of it entirerly.*)
  Lemma steps_extend_trace f n1 n2 :
    n1 <= n2 ->
    (forall i, n1 <= i < n2 -> o2 state_step (f i) (f (S i))) ->
    exists k'', oget_trace (f n2) = k'' ++ oget_trace (f n1).
  Proof.
    intros H1. replace n2 with ((n2 - n1) + n1) by lia.
    induction (n2 - n1).
    - intros _. exists nil. reflexivity.
    - intros H. eassert (hyp : _). 2: specialize (IHn hyp); clear hyp.
      { intros. apply H. lia. }
      fwd. specialize (H (n + n1) ltac:(lia)). apply ostep_extends_trace in H. fwd.
      eexists. simpl. rewrite H. trace_alignment. eassumption.
  Qed.

  Lemma other_steps_extend_trace f n1 n2 :
    possible_execution f ->
    n1 <= n2 ->
    f n2 = None \/ exists k'', oget_trace (f n2)  = k'' ++ oget_trace (f n1).
  Proof.
    intros H0 H1. replace n2 with ((n2 - n1) + n1) by lia.
    induction (n2 - n1).
    - right. exists nil. reflexivity.
    - fwd. specialize (H0 (n + n1)). destruct H0 as [H0|[H0|H0]]; destruct IHn as [IHn|IHn].
      + cbv [step_ostate] in H0. rewrite IHn in H0. destruct H0.
      + fwd. right.
        enough (exists k''0, oget_trace (f (S n + n1)) = k''0 ++ oget_trace (f (n + n1))).
        { fwd. eexists. rewrite H, IHn. rewrite app_assoc. reflexivity. }
        apply ostep_extends_trace. apply H0.
      + cbv [stuck_ostate] in H0. rewrite IHn in H0. destruct H0 as [[] _].
      + left. cbv [stuck_ostate] in H0. fwd. assumption.
      + fwd. left. assumption.
      + fwd. left. assumption.
  Qed.

  (*Lemma get_long_trace_small_enough f fuel :
    possible_execution f ->
    forall i, i < get_long_trace f fuel -> step_ostate f i.
  Proof.
    intros H i Hi. induction fuel.
    - simpl in Hi. lia.
    - simpl in Hi. destruct (f (S fuel)) eqn:EfSf.
      + eapply step_until_stuck; eauto. rewrite EfSf. congruence.
      + auto.
  Qed.
  
  Lemma get_long_trace_big_enough f fuel :
    possible_execution f ->
    forall i,
      get_long_trace f fuel < i <= fuel ->
      f i = None.
  Proof.
    intros H i Hi. induction fuel.
    - simpl in Hi. lia.
    - simpl in Hi. destruct (f (S fuel)) eqn:EfSf.
      + lia.
      + assert (i = S fuel \/ i <= fuel) by lia. destruct H0; [subst; assumption|].
        apply IHfuel. lia.
  Qed.*)

  Lemma get_long_trace_works' f fuel :
    possible_execution f ->
    forall n,
      length (oget_trace (f n)) <= length (oget_trace (f fuel)) \/ f fuel = None ->
      exists k'', oget_trace (f (get_long_trace f fuel)) = k'' ++ oget_trace (f n).
  Proof.
    intros H n Hn. induction fuel.
    - simpl. Check other_steps_extend_trace. destruct Hn as [Hn|Hn].
      + assert (Hle : O <= n) by lia. apply (other_steps_extend_trace _ _ _ H) in Hle.
        destruct Hle as [Hle|Hle].
        -- rewrite Hle. eexists. rewrite app_nil_r. reflexivity.
        -- fwd. rewrite Hle in Hn. rewrite app_length in Hn. destruct k''; [|simpl in Hn; lia].
           rewrite Hle. exists nil. reflexivity.
      + enough (f n = None). { rewrite H0. eexists. rewrite app_nil_r. reflexivity. }
        eapply done_stable; eauto. lia.
    - simpl. destruct Hn as [Hn|Hn].
      + clear IHfuel. assert (Hle: n <= S fuel \/ S fuel <= n) by lia.
        destruct (f (S fuel)) as [fSf|] eqn:EfSf.
        2: { destruct (oget_trace (f n)); [|simpl in Hn; lia].
             eexists. rewrite app_nil_r. reflexivity. }
        rewrite EfSf. destruct Hle as [Hle|Hle].
        -- apply (other_steps_extend_trace _ _ _ H) in Hle. destruct Hle as [Hle|Hle]; [congruence|].
           rewrite EfSf in Hle. apply Hle.
        -- assert (Hle' := Hle). apply (other_steps_extend_trace _ _ _ H) in Hle.
           destruct Hle as [Hle|Hle].
           { rewrite Hle. eexists. rewrite app_nil_r. reflexivity. }
           fwd. rewrite Hle in Hn. rewrite app_length in Hn. rewrite EfSf in Hn.
           destruct k''; [|simpl in Hn; lia]. rewrite Hle. exists nil. rewrite EfSf. reflexivity.
      + rewrite Hn. apply IHfuel. clear IHfuel.
        assert (Hle : n <= fuel \/ fuel < n) by lia. destruct Hle as [Hle|Hle].
        -- apply (other_steps_extend_trace _ _ _ H) in Hle. destruct Hle as [Hle|Hle].
           ++ right. assumption.
           ++ left. fwd. rewrite Hle. rewrite app_length. lia.
        -- left. enough (H0: f n = None). { rewrite H0. simpl. lia. }
           eapply done_stable; eauto.
  Qed.

  Lemma get_long_trace_works f n :
    possible_execution f ->
    exists k'',
    oget_trace (f (get_long_trace f (enough_distance f O (length (oget_trace (f n)))))) = k'' ++ oget_trace (f n).
  Proof. Check its_enough.
    intros H. apply get_long_trace_works'; try assumption.
    apply (its_enough f O (length (oget_trace (f n)))) in H.
    destruct H as [H|H].
         - right. assumption.
         - left. lia.
  Qed.

  Definition trace_with_length f n :=
    rev (firstn n (rev (oget_trace (f (get_long_trace f (enough_distance f O n)))))).

  Lemma trace_with_length_works f i :
    possible_execution f ->
    trace_with_length f (length (oget_trace (f i))) = oget_trace (f i).
  Proof.
    intros H. apply (get_long_trace_works f i) in H. fwd.
    cbv [trace_with_length]. rewrite H. rewrite rev_app_distr.
    rewrite List.firstn_app_l.
    2: { rewrite rev_length. reflexivity. }
    rewrite rev_involutive. reflexivity.
  Qed.

  Fixpoint predictor_of_trace (k : trace) (k' : trace) : event :=
    match k, k' with
    | e :: k, nil => e
    | _ :: k, _ :: k' => predictor_of_trace k k'
    | _, _ => leak_unit
    end.

  Lemma predictor_of_trace_works k :
    predicts (predictor_of_trace k) k.
  Proof.
    induction k.
    - constructor.
    - constructor.
      + reflexivity.
      + assumption.
  Qed.

  Definition predictor_of_execution f k :=
    predictor_of_trace (trace_with_length f (length k)) k.

  Lemma predictor_of_exectution_works f k :
    predicts (predictor_of_execution f) (oget_trace (f k)).
  Proof.
    cbv [predictor_of_execution]. Search predicts. eapply predicts_ext.
    { rewrite trace_with_length_works.
  
  End choice_and_middle.
  End WithDet.
  Print possible_execution.
  Definition possible_execution_det {pick_sp : PickSp} := possible_execution true.
  Definition satisfies_det {pick_sp : PickSp} := satisfies true.
  Definition possible_execution_nondet {pick_sp : PickSp} := possible_execution false.
  Definition satisfies_nondet {pick_sp : PickSp} := satisfies false. Check predicts.
  Implicit Types post : trace -> io_trace -> mem -> locals -> metrics -> Prop.

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

  (*Lemma state_stuck_nondet_det {pick_sp : PickSp} st :
    state_stuck false st -> state_stuck true st.
  Proof.
    intros H1 H2. apply H1. clear H1. fwd. exists st'.*)

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

  Lemma predicts_app_inv k1 k2 f :
    predicts f (k1 ++ k2) ->
    predicts f k1 /\ predicts (fun k => f (k1 ++ k)) k2.
  Proof.
    intros H. revert f H. induction k1.
    - intros f H. split; [constructor|assumption].
    - intros f H. inversion H. subst. apply IHk1 in H4. fwd. split.
      + constructor; assumption.
      + assumption.
  Qed.      
    
  Lemma step_state_equiv {pick_sp : PickSp} st st' :
    state_step true st st' <->
      (state_step false st st' /\
         exists k'',
           get_trace st' = k'' ++ get_trace st /\
             predicts (fun k_ => consume_word (pick_sp (rev k_ ++ get_trace st))) (List.rev k'')).
  Proof.
    destr_sstate st. destr_sstate st'. subst. simpl. split.
    { intros H; induction H; fwd.
      all: try (split; [econstructor; eauto|]).
      all: try (subst_exprs; eexists; split; [solve [trace_alignment]|]).
      all: repeat rewrite app_nil_r; simpl.
      all: try (apply predicts_trivially; intros;
                repeat (rewrite in_app_iff || rewrite <- in_rev || simpl);
                intuition eauto; congruence).
      - constructor.
        + intros _. specialize (H0 eq_refl). subst. reflexivity.
        + constructor.
      - assumption. }
    { intros [H1 H2]. revert H2. induction H1; intros; fwd; try (econstructor; eauto).
      intros _.
      replace (consume_word a :: k) with ((consume_word a :: nil) ++ k) in H3p0 by reflexivity.
      apply app_inv_tail in H3p0. subst. simpl in H3p1. inversion H3p1. subst.
      simpl in H6. specialize (H6 I). inversion H6. subst. reflexivity. }
  Qed.

  Lemma step_ostate_equiv {pick_sp : PickSp} f i :
    step_ostate true f i <->
      (step_ostate false f i /\
         exists k'',
           oget_trace (f (S i)) = k'' ++ oget_trace (f i) /\
             predicts (fun k_ => consume_word (pick_sp (rev k_ ++ oget_trace (f i)))) (List.rev k'')).
  Proof.
    cbv [step_ostate]. split.
    - intros H.
      destruct (f i) as [fi|]; [|destruct H]. destruct (f (S i)) as [fSi|]; [|destruct H].
      simpl in H. rewrite step_state_equiv in H. simpl. apply H.
    - intros H.
      destruct (f i) as [fi|]; [|destruct H as [H _]; destruct H].
      destruct (f (S i)) as [fSi|]; [|destruct H as [H _]; destruct H].
      simpl. rewrite step_state_equiv. apply H.
  Qed.

  Lemma step_ostates_equiv {pick_sp : PickSp} f n :
    (forall i, i < n -> step_ostate true f i) <->
      ((forall i, i < n -> step_ostate false f i) /\
         exists k'',
           oget_trace (f n) = k'' ++ oget_trace (f O) /\
             predicts (fun k_ => consume_word (pick_sp (rev k_ ++ oget_trace (f O)))) (rev k'')).
  Proof.
    induction n.
    - split.
      + intros H. split.
        -- intros. lia.
        -- destruct (f O) as [f0|]; simpl.
           2: { exists nil. intuition. constructor. }
           eexists; split; [f_equal;trace_alignment|]. constructor.
      + intros. lia.
    - split.
      + destruct IHn as [IHn _]. intros H. eassert (hyp : _). 2: specialize (IHn hyp); clear hyp.
        { intros. apply H. lia. }
        fwd. split.
        -- intros. specialize (H i ltac:(lia)). rewrite step_ostate_equiv in H. fwd. assumption.
        -- specialize (H n ltac:(lia)). rewrite step_ostate_equiv in H.
           destruct H as [_ H]. fwd. eexists. split.
           { rewrite Hp0. rewrite IHnp1p0. trace_alignment. }
           rewrite app_nil_r. rewrite rev_app_distr. apply predicts_app.
           ++ assumption.
           ++ eapply predicts_ext. 2: eassumption. simpl. intros. f_equal. f_equal.
              rewrite rev_app_distr. rewrite rev_involutive. repeat rewrite <- app_assoc.
              rewrite IHnp1p0. reflexivity.
      + destruct IHn as [_ IHn]. intros H. fwd.
        assert (H' := steps_extend_trace false f O n ltac:(lia)).
        eassert (hyp : _). 2: specialize (H' hyp); clear hyp.
        { intros. apply Hp0. lia. }
        assert (extend := Hp0 n ltac:(lia)). apply ostep_extends_trace in extend.
        fwd. rewrite extend in Hp1p0. rewrite H' in Hp1p0. rewrite app_assoc in Hp1p0.
        apply app_inv_tail in Hp1p0. subst.
        rewrite rev_app_distr in Hp1p1.
        apply predicts_app_inv in Hp1p1. fwd.
        eassert (hyp : _). 2: specialize (IHn hyp); clear hyp.
        { split.
          - intros. apply Hp0. lia.
          - fwd. exists k''1. split; assumption. }
        intros. destruct (Nat.ltb i n) eqn:E.
        { apply PeanoNat.Nat.ltb_lt in E. apply IHn. assumption. }
        apply PeanoNat.Nat.ltb_nlt in E. assert (i = n) by lia. subst. clear E H.
        rewrite step_ostate_equiv. split.
        { apply Hp0. lia. }
        exists k''0. split; [assumption|].
        eapply predicts_ext. 2: eassumption. simpl. intros. rewrite rev_app_distr.
        rewrite rev_involutive. repeat rewrite <- app_assoc. rewrite H'. reflexivity.
  Qed.

  Lemma forall_through_and {A : Type} (P Q : A -> Prop) :
    (forall n, P n) /\ (forall n, Q n) <-> forall n, P n /\ Q n.
  Proof.
    split; intros; fwd; try tauto. 1: split; auto. split; intros n; specialize (H n); fwd; auto.
  Qed.
  
  (*this is not true.  see what happens if f gets stuck deterministically but not nondeterministically*)
  (*Lemma poss_det_nondet {pick_sp : PickSp} f :
    possible_execution_det f <->
      (possible_execution_nondet f /\ forall n,
        exists k'',
          get_trace (f (S n)) = k'' ++ get_trace (f O) /\
            predicts (fun k_ => consume_word (pick_sp (rev k_ ++ get_trace (f O)))) (rev k'')).
  Proof. Abort.*)
  
  Lemma nondet_stuck_det_stuck {pick_sp : PickSp} st :
    state_stuck false st -> state_stuck true st.
  Proof.
    intros H H'. apply H. fwd. rewrite step_state_equiv in H'. exists st'. fwd. assumption.
  Qed.
    

  Lemma nondet_good_stuck_det_good_stuck {pick_sp : PickSp} st :
    good_stuck false st -> good_stuck true st.
  Proof.
    intros H. induction H; econstructor; eauto using nondet_stuck_det_stuck.
  Qed.

  Lemma stuck_not_nondet_stuck_good {pick_sp : PickSp} st :
    excluded_middle ->
    state_stuck true st ->
    ~state_stuck false st ->
    good_stuck true st.
  Proof.
    intros em H1 H2. Search (~exists _, _). cbv [state_stuck] in H2. Search (~ ~ _).
    apply Decidable.not_not in H2. 2: { apply em. } destruct H2 as [st' H2].
    destr_sstate st. destr_sstate st'. subst. induction H2; intros.
    all: try (exfalso; apply H1; eexists (_, _, _, _, _, _); econstructor; solve [eauto]).
    - econstructor; eauto.
    - constructor. apply IHstep. intros H'. apply H1. destruct H' as [st' H'].
      destr_sstate st'. eexists (_, _, _, _, _, _). eapply seq_step. eassumption.
  Qed.

  Lemma good_nondet_stuck_good {pick_sp : PickSp} st :
    good_stuck true st ->
    state_stuck false st ->
    good_stuck false st.
  Proof.
    intros H1 H2. induction H1; try solve [econstructor; eauto].
    econstructor; eauto. apply IHgood_stuck. intros H'. apply H2. fwd. destr_sstate st'.
    eexists (_, _, _, _, _, _). eapply seq_step. eassumption.
  Qed.

  Lemma pick_sp_irrelevant (pick_sp1 pick_sp2 : PickSp) st st' :
    state_step (pick_sp := pick_sp1) false st st' ->
    state_step (pick_sp := pick_sp2) false st st'.
  Proof.
    intros H. destr_sstate st. destr_sstate st'. subst. induction H; econstructor; eauto.
    congruence.
  Qed.

  Lemma option_pick_sp_irrelevant (pick_sp1 pick_sp2 : PickSp) f i :
    step_ostate (pick_sp := pick_sp1) false f i ->
    step_ostate (pick_sp := pick_sp2) false f i.
  Proof.
    cbv [step_ostate]. destruct (f i), (f (S i)); try intros []. apply pick_sp_irrelevant. Qed.
 
  Lemma nondet_to_det {pick_sp : PickSp} s k t m l mc post f :
    excluded_middle ->
    f O = Some (s, k, t, m, l, mc) ->
    (possible_execution_nondet f ->
     satisfies_nondet f (fun k' t' m' l' mc' =>
                           exists k'',(*if I write forall k'' here, can I avoid the extends_trace lemmas?*)
                             k' = k'' ++ k /\
                               (predicts (fun k_ => consume_word (pick_sp (rev k_ ++ k))) (List.rev k'') ->
                                post k' t' m' l' mc'))) ->
    possible_execution_det f ->
    satisfies_det f post.
  Proof.
    intros em HfO H Hfposs. assert (nondet_or_not := em (possible_execution_nondet f)).
    destruct nondet_or_not as [nondet|not].
    - specialize (H ltac:(eassumption)). cbv [satisfies_nondet] in H.
      destruct H as [n H]. destruct (f n) as [fn|] eqn:Efn; [|destruct H]. destr_sstate fn.
      subst. simpl in H. destruct H as [H|H].
      + (*both succeed*)
        fwd. assert (Hsteps : forall i, i < n -> step_ostate true f i).
        { Search step_ostate. apply step_until_stuck; try assumption. congruence. }
        rewrite step_ostates_equiv in Hsteps. fwd.
        exists n. rewrite Efn. simpl. cbv [state_satisfies]. left. intuition.
        apply Hp1p1. rewrite HfO in Hstepsp1p1. rewrite HfO, Efn in Hstepsp1p0.
        simpl in Hstepsp1p0. apply app_inv_tail in Hstepsp1p0. subst.
        simpl in Hstepsp1p1. apply Hstepsp1p1.
      + (*both good stuck*)
        exists n. rewrite Efn. right. specialize (nondet n).
        apply nondet_good_stuck_det_good_stuck. assumption.
    - (*this means that f got stuck deterministically but not nondeterministically*)
      Search (~(forall _, _)). apply (naen em) in not. destruct not as [y not].
      Search (~(_ \/ _)). apply Decidable.not_or in not. fwd. apply Decidable.not_or in notp1.
      fwd. specialize (Hfposs y). destruct Hfposs as [Hfposs|[Hfposs|Hfposs]].
      + exfalso. apply notp0. rewrite step_ostate_equiv in Hfposs. fwd. eassumption.
      + cbv [stuck_ostate] in Hfposs. cbv [stuck_ostate] in notp1p0. fwd.
        assert (notp1p0' : ~o1 (state_stuck false) (f y)) by auto. clear notp1p0.
        exists y. destruct (f y) as [fy|]; [|destruct Hfpossp0]. right.
        apply stuck_not_nondet_stuck_good; assumption.
      + exfalso. auto.
  Qed.
  
  Lemma no_nones_steps {pick_sp : PickSp} f :
    possible_execution_nondet f ->
    (forall i, f i <> None) ->
    forall j, step_ostate false f j.
  Proof.
    intros H1 H2 j. specialize (H1 j). destruct H1 as [H1|[H1|H1]].
    - assumption.
    - destruct H1 as [_ H1]. apply H2 in H1. destruct H1.
    - fwd. apply H2 in H1p0. destruct H1p0.
  Qed.

  Check invert_seq.
  
  (*Lemma trace_gets_longer_seq {pick_sp : PickSp} f i :
    if all executions starting with s1 and s2 eventually get a longer trace,
    then the same goes for sseq s1 s2.*)
  

  (*Lemma trace_gets_longer {pick_sp : PickSp} f i :
    possible_execution_nondet f ->
    (forall j, f j <> None) ->
    exists j, length (val_def nil (option_map get_trace (f j))) > length (val_def nil (option_map get_trace (f i))).
  Proof.
    intros H1 H2. destruct (f i) as [fi|] eqn:E.
    2: { apply H2 in E. destruct E. }
    destr_sstate fi. subst. revert i k t m l mc E.
    induction s; intros.
    all: assert (steps := no_nones_steps f H1 H2).
    all: assert (stepi := steps i); assert (stepSi := steps (S i)).
    all: cbv [step_ostate] in stepi, stepSi.
    all: destruct (f (S i)) as [fSi|] eqn:E1; [|apply H2 in E1; destruct E1].
    all: destruct (f (S (S i))) as [fSSi|] eqn:E2; [|apply H2 in E2; destruct E2].
    all: destr_sstate fSi; destr_sstate fSSi; rewrite E in *; subst; simpl in *.
    { inversion stepi; subst. }
    all: try solve [inversion stepi; subst; inversion stepSi].
    - inversion stepi. subst. Admitted.

  Lemma pick_sp_exists {pick_sp : PickSp} f :
    possible_execution_nondet f ->
    exists pick_sp',
      possible_execution_det (pick_sp := pick_sp') f.
  Proof. Admitted.*)

  Lemma det_to_nondet {pick_sp  : PickSp} s k t m l mc post f :
    excluded_middle ->
    f O = Some (s, k, t, m, l, mc) ->
    possible_execution_nondet f ->
    (possible_execution_det (pick_sp := (fun k => match predictor_of_execution f (rev k) with
                                                  | consume_word w => w
                                                  | _ => word.of_Z 0
                                                  end)) f ->
     satisfies_det f post) ->
    satisfies_nondet f (fun k' t' m' l' mc' =>
                          exists k'',(*if I write forall k'' here, can I avoid the extends_trace lemmas?*)
                            k' = k'' ++ k /\
                              (predicts (fun k_ => consume_word (pick_sp (rev k_ ++ k))) (List.rev k'') ->
                               post k' t' m' l' mc')).
  Proof.
    intros em HfO Hposs. intros H. specialize (H det).
    destruct H as [n H]. exists n.
    destruct (f n) as [fn|] eqn:Efn; [|destruct H]. simpl. destr_sstate fn. simpl in H.
    specialize satisfies_stuck with (1 := H). intros Hstuck. Check step_until_stuck.
    assert (Hsteps : forall m, m < n -> step_ostate true f m).
    { apply step_until_stuck; [assumption|congruence]. }
    rewrite step_ostates_equiv in Hsteps. fwd. rewrite HfO, Efn in Hstepsp1p0.
    simpl in Hstepsp1p0. subst. rewrite HfO in Hstepsp1p1. simpl in Hstepsp1p1.
    destruct H as [H|H].
    + (*both succeed*) fwd. left. intuition. eexists; eauto.
    + (*both good stuck*) right. assert (Hnone: f (S n) = None).
      { specialize (det n). destruct det as [det|[det|det]].
        - exfalso. eapply good_stuck_stuck; try eassumption. cbv [step_ostate] in det.
          rewrite Efn in det. destruct (f (S n)) as [fSn|]; [|destruct det].
          eexists. eassumption.
        - cbv [stuck_ostate] in det. fwd. assumption.
        - fwd. assumption. }
      specialize (Hposs n). destruct Hposs as [Hposs|[Hposs|Hposs]].
      -- exfalso. cbv [step_ostate] in Hposs. rewrite Hnone in Hposs.
         destruct (f n); destruct Hposs.
      -- (*if stuck, then good stuck*)
        cbv [stuck_ostate] in Hposs. fwd. rewrite Efn in Hpossp0. simpl in Hpossp0.
        eapply good_nondet_stuck_good; try assumption.
        -- exfalso. fwd. congruence.
    - (*f took some step that was allowable nondeterministically but not deterministically*)
      apply (naen em) in not. destruct not as [y not]. specialize (H f HfO Hposs). specialize (Hposs y).
      
            induction H; try solve [econstructor; eauto]. { econstructor; eauto. (**)eapply stuck_not_nondet_stuck_good. _stuck_det_good_stuck. eapply good_stuck_stuck in ; try eassumption. cbv [state_
        nspecialize (Hposs n). destruct Hposs as [Hposs|[Hposs|Hposs]]. 
        -- Search (
        right. subst.
      left.
      apply app_inv_tail in Hstepsp1p0.
      subst.
      Search state_satisfies.
      destruct H as [H|H].
      + (*both succeed*) fwd. left. intuition. rewrite 
  
End exec.

(*forall (f : nat -> _),
  f O = (inclusion s, k, t, m, l, mc) ->
  possible_execution f ->
  satisfies f post*)

Print exec.possible_execution.


Definition possible_execution_det := 



Lemma small_steps_same

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
