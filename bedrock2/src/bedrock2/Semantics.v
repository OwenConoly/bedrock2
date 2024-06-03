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
  | end_interact (binds : list String.string) (action : String.string) (args : list word) (mKeep mGive mReceive : mem) (resvals klist : list word)
  | terminated.
  
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

  Definition state_step st1 st2 :=
    let '(s1, k1, t1, m1, l1, mc1) := st1 in
    let '(s2, k2, t2, m2, l2, mc2) := st2 in
    step s1 k1 t1 m1 l1 mc1 s2 k2 t2 m2 l2 mc2.

  Definition done_state f i :=
    get_scmd (f i) = sskip /\ get_scmd (f (S i)) = terminated.

  Definition state_stuck st :=
    ~exists st', state_step st st'.

  Definition stuck_state f i :=
    state_stuck (f i) /\ get_scmd (f (S i)) = terminated.

  Definition step_state f i :=
    state_step (f i) (f (S i)).

  Definition possible_execution (f : nat -> sstate) :=
    forall i, step_state f i \/ stuck_state f i.

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

  Definition state_satisfies st post : Prop :=
    (let '(s, k, t, m, l, mc) := st in s = sskip /\ post k t m l mc) \/
      good_stuck st.

  Definition satisfies (f : nat -> _) post := exists i, state_satisfies (f i) post.
  
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

  Definition a_terminated_state : sstate :=
    (terminated, nil, nil, map.empty, map.empty, EmptyMetricLog).

  Definition first_part st : sstate :=
    match st with
    | (sseq s1 s2, k, t, m, l, mc) => (s1, k, t, m, l, mc)
    | _ => a_terminated_state (*this is just some dummy value here*)
    end.
  
  Fixpoint execution_of_first_part (f : nat -> sstate) n :=
    match n with
    | O => first_part (f O)
    | S n' =>
        match (execution_of_first_part f n') with
        | (sskip, _, _, _, _, _) => a_terminated_state
        | (terminated, _, _, _, _, _) => a_terminated_state
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
        (choice : FunctionalChoice_on sstate sstate).

  Lemma sskip_or_first_part' f n :
    match (execution_of_first_part f n) with
    | (sskip, _, _, _, _, _) => True
    | (terminated, _, _, _, _, _) => True
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

  Lemma sskip_terminated_or_first_part f n :
    get_scmd (execution_of_first_part f n) = sskip \/ get_scmd (execution_of_first_part f n) = terminated \/ first_part (f n) = execution_of_first_part f n.
  Proof.
    assert (H := sskip_or_first_part' f n). destr_sstate (execution_of_first_part f n).
    destruct s; auto.
  Qed.
  
  Lemma possible_first_part f :
    possible_execution f ->
    possible_execution (execution_of_first_part f).
  Proof.
    cbv [possible_execution]. intros H n.
    specialize (H n). assert (H1 := sskip_terminated_or_first_part f n).
    destruct H1 as [H1 | [H1 | H1]].
    - destr_sstate (execution_of_first_part f n). simpl in H1. subst.
      right. cbv [stuck_state]. split.
      + intros [st H']. rewrite Ef in H'. cbv [state_step step_state] in H'.
        destr_sstate st. inversion H'.
      + simpl. rewrite Ef. reflexivity.
    - destr_sstate (execution_of_first_part f n). simpl in H1. subst.
      right. cbv [stuck_state]. split.
      + intros [st H']. rewrite Ef in H'. cbv [state_step step_state] in H'.
        destr_sstate st. inversion H'.
      + simpl. rewrite Ef. reflexivity.
    - destruct H as [H | H].
      + cbv [step_state state_step] in H. destr_sstate (f n).
        destr_sstate (execution_of_first_part f n).
        assert (H0 : s0 = terminated \/ exists s1 s2, s = sseq s1 s2).
        { destruct s; destruct s0; simpl in H1; cbv [a_terminated_state] in H1; try congruence.
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
           all: cycle -1.
           { right. cbv [stuck_state]. inversion H; subst. inversion H14. }
           all: left; inversion H; subst; cbv [step_state state_step]; simpl; rewrite Ef0;
             rewrite Ef1; simpl; assumption.
      + right. destruct H as [Hp1 Hp2]. split.
        -- intros [st H']. apply Hp1. clear Hp1 Hp2. rewrite <- H1 in H'. clear H1.
           cbv [state_step step_state] in *. destr_sstate (f n).           
           destr_sstate st. destruct s; simpl in H'; try solve [inversion H'].
           eexists (_, _, _, _, _, _). econstructor. eassumption.
        -- simpl. destr_sstate (f (S n)). simpl in Hp2. subst.
           destr_sstate (execution_of_first_part f n). destruct s; reflexivity.
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

  (*I think we don't actually need em for this, but I don't care to prove it without it.*)
  Lemma sstate_eq_dec (st1 st2 : sstate) :
    st1 = st2 \/ st1 <> st2.
  Proof. apply em. Qed.

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
    state_satisfies st post ->
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

  Lemma stuck_stable f n :
    possible_execution f ->
    state_stuck (f n) ->
    forall m, n < m ->
              get_scmd (f m) = terminated.
  Proof.
    intros H1 H2 m Hm. induction m.
    - lia.
    - destruct (Nat.ltb n m) eqn:E.
      + apply PeanoNat.Nat.leb_le in E. specialize (IHm E). specialize (H1 m).
        destr_sstate (f m). destr_sstate (f (S m)). simpl in *. subst.
        destruct H1 as [H1|H1].
        { exfalso. cbv [step_state state_step] in H1. rewrite Ef, Ef0 in H1. inversion H1. }
        cbv [stuck_state] in H1. fwd. rewrite Ef0 in H1p1. simpl in H1p1. subst. reflexivity.
      + apply PeanoNat.Nat.ltb_nlt in E. assert (n = m) by lia. subst.
        destruct (H1 m).
        { exfalso. eapply step_not_stuck; eassumption. }
        destruct H. assumption.
  Qed.

  (*Lemma min_satisfies f n post :
    possible_execution f ->
    state_satisfies (f n) post ->
    exists m,
      state_satisfies (f m) post /\
        forall i, i < m -> step_state f i.
  Proof.
    intros H1 H2. assert (H := nats_have_mins n (fun n => state_satisfies (f n) post)).
    simpl in H. specialize (H (fun i => em _) H2). clear n H2. fwd. exists m.
    split; [assumption|]. intros i H. destruct (H1 i) as [H1'|H1']; try assumption.
    exfalso. eapply Hp1; try eassumption. cbv [stuck_state] in H1'. destruct H1' as [H1' H2'].
    assert (H' := stuck_stable _ _ H1 H1'). specialize (H' m ltac:(lia)). rewrite <- H'.
    assumption.
  Qed.*)

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

  (*why do we care*)
  Lemma execution_of_first_part_stable' f n :
    get_scmd (execution_of_first_part f n) = sskip ->
    forall m, n < m ->
               get_scmd (execution_of_first_part f m) = terminated.
  Proof.
    intros. Admitted. (*replace m with ((m - n) + n) by lia. clear H0.
    induction (m - n).
    - reflexivity.
    - simpl. rewrite <- IHn0. clear IHn0.
      destr_sstate (execution_of_first_part f n). simpl in H. subst.
      reflexivity.
  Qed.*)

  Lemma first_part_1 f i :
    get_scmd (execution_of_first_part f i) <> terminated ->
    execution_of_first_part f i = first_part (f i).
  Proof.
    intros H. destruct i.
    - reflexivity.
    - simpl in *. destr_sstate (execution_of_first_part f i).
      destruct s; try reflexivity.
      all: cbv [a_terminated_state] in H; simpl in H; congruence.
  Qed.

  Definition append (st : sstate) s' :=
    let '(s, k, t, m, l, mc) := st in (sseq s s', k, t, m, l, mc).

  Lemma second_comes_after_first s1 s2 k t m l mc k' t' m' l' mc' f i :
    f O = (sseq s1 s2, k, t, m, l, mc) ->
    possible_execution f ->
    execution_of_first_part f i = (sskip, k', t', m', l', mc') ->
    f (S i) = (s2, k', t', m', l', mc').
  Proof.
    intros H1 H2 H3.
    assert (forall n, n <= i -> f n = append (execution_of_first_part f n) s2). (*this deserves to be its own lemma*)
    { intros n. induction n.
      - intros. simpl. rewrite H1. reflexivity.
      - intros H. specialize (IHn ltac:(lia)). assert (Hn := H2 n). destruct Hn as [Hn|Hn].
        + simpl. destr_sstate (execution_of_first_part f n). simpl in IHn.
          cbv [step_state] in Hn. rewrite IHn in Hn. destr_sstate (f (S n)).
          inversion Hn; subst.
          -- inversion H16; reflexivity.
          -- exfalso. assert (H' := execution_of_first_part_stable').
             specialize (H' f n). rewrite Ef in H'. specialize (H' eq_refl i ltac:(lia)).
             rewrite H3 in H'. simpl in H'. discriminate H'.
        + cbv [stuck_state] in Hn. fwd. assert (Hstuck := stuck_stable _ _ H2 Hnp0).
          specialize (Hstuck i ltac:(lia)). destruct i as [|i]; [lia|].
          simpl in H3. destr_sstate (execution_of_first_part f i). destr_sstate (f (S i)).
          simpl in Hstuck. subst. simpl in H3. destruct s; discriminate H3. }
    specialize (H i ltac:(lia)). rewrite H3 in H. simpl in H. specialize (H2 i).
    destruct H2 as [H2|H2].
    2: { exfalso. destruct H2 as [stuck eq]. apply stuck. eexists (_, _, _, _, _, _).
         rewrite H. apply seq_done_step. }
    cbv [step_state] in H2. rewrite H in H2. destr_sstate (f (S i)). inversion H2; subst.
    - inversion H16.
    - reflexivity.
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
      specialize (H2 (fun j => f (S i + j))).
      simpl in H2. replace (i + 0) with i in H2 by lia.
      replace (fun j => f (S (i + j))) with (fun j => f (S i + j)) in H2 by reflexivity.
      specialize (H2 H3 (possible_execution_offset _ _ H1)).
      eapply satisfies_offset. eapply H2.
    - rewrite first_part_1 in H.
      + remember (first_part (f i)) as st eqn:E. cbv [satisfies]. exists i.
        cbv [state_satisfies]. right. destr_sstate (f i). destruct H.
        -- destruct s; simpl in E; cbv [a_terminated_state] in E; try congruence.
           inversion E. subst. clear E. constructor. constructor.
           ++ assumption.
           ++ assumption.
        -- destruct s; simpl in E; cbv [a_terminated_state] in E; try congruence.
           inversion E. subst. clear E. constructor. econstructor; eassumption.
        -- destruct s; simpl in E; cbv [a_terminated_state] in E; try congruence.
           inversion E. subst. clear E. constructor. constructor; assumption.
        -- destruct s; simpl in E; cbv [a_terminated_state] in E; try congruence.
           inversion E. subst. clear E. constructor. constructor. assumption.
     + destr_sstate (execution_of_first_part f i). destruct s; simpl; try congruence.
        inversion H.
  Qed.

  Definition execute_with_tail (f : nat -> sstate) (s2 : scmd) (n : nat) : sstate :=
    let '(s, k, t, m, l, mc) := f n in
    (sseq s s2, k, t, m, l, mc).

  Print done_state.

  Lemma step_until_stuck f n :
    possible_execution f ->
    get_scmd (f n) <> terminated ->
    forall m, m < n -> step_state f m.
  Proof.
    intros H1 H2. intros. assert (Hm := H1 m). destruct Hm as [Hm|Hm]; [assumption|].
    exfalso. apply H2. eapply stuck_stable; try eassumption. destruct Hm. assumption.
  Qed.

  (*TODO (to make my proofs less long and repetitive): write a lemma that says
    satisfies f post -> forall i, get_scmd (f i) = sskip -> post (f i).*)

  Fixpoint repeat_f {A: Type} (f : A -> A) x n :=
    match n with
    | O => x
    | S n' => f (repeat_f f x n')
    end.

  Lemma possible_execution_exists st :
    exists f, f O = st /\ possible_execution f.
  Proof.
    cbv [possible_execution step_state stuck_state].
    assert (Hnext : exists (next : sstate -> sstate), forall st,
               state_step st (next st) \/ state_stuck st /\ get_scmd (next st) = terminated).
    { clear -choice em. cbv [FunctionalChoice_on] in choice. apply (choice (fun st st' => state_step st st' \/ state_stuck st /\ get_scmd st' = terminated)).
      intros st. assert (step_or_not := em (exists st', state_step st st')).
      destruct step_or_not as [step|not].
      - destruct step as [st' step]. exists st'. left. assumption.
      - exists a_terminated_state. right. split; [|reflexivity]. cbv [state_stuck]. apply not. }
    destruct Hnext as [next Hnext]. Print repeat_f.
    exists (fun n => repeat_f next st n). split; [reflexivity|]. intros.
    apply Hnext.
  Qed.

  Lemma later_comes_after f i j :
    possible_execution f ->
    step_state f i ->
    get_scmd (f j) <> terminated ->
    i < j ->
    comes_after (f j) (f i).
  Proof.
    intros H1 H2 H3. induction j.
    - lia.
    - destruct (Nat.ltb i j) eqn:E.
      + apply PeanoNat.Nat.ltb_lt in E. eassert (hyp : _). 2: specialize (IHj hyp); clear hyp.
        { intros H. apply H3. apply (stuck_stable _ j); try assumption; try lia.
          destr_sstate (f j). simpl in H. subst. intros H. destruct H as [st' H].
          destr_sstate st'. inversion H. }
        intros H. specialize (IHj ltac:(lia)). specialize (H1 j). destruct H1 as [H1|H1].
        -- eapply t_trans. 2: eassumption. apply t_step. apply H1.
        -- destruct H1 as [_ H1]. exfalso. auto.
      + intros. apply PeanoNat.Nat.ltb_nlt in E. replace j with i by lia. apply t_step. apply H2.
  Qed.

  Lemma comes_after_seq' st st' s :
      comes_after st' st ->
      comes_after (append st' s) (append st s).
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
        f O = (sseq s1 s2, k, t, m, l, mc) ->
        possible_execution f ->
        satisfies f post) ->
    (forall (f : nat -> _),
        f O = (s1, k, t, m, l, mc) ->
        possible_execution f ->
        satisfies f (fun k' t' m' l' mc' =>
                       comes_after (s2, k', t', m', l', mc') (sseq s1 s2, k, t, m, l, mc) /\
                         forall (g : nat -> _),
                           g O = (s2, k', t', m', l', mc') ->
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
    assert (terminates_or_not := em (exists n, get_scmd (f n) = sskip)).
    destruct terminates_or_not as [terminates|not].
    2: { assert (Hseqposs : possible_execution (execute_with_tail f s2)).
         { intros n. specialize (Hfposs n).
           cbv [step_state state_step stuck_state] in *. cbv [execute_with_tail].
           destr_sstate (f n). destr_sstate (f (S n)).
           destruct Hfposs as [Hfposs|Hfposs].
           - left. apply seq_step. assumption.
           - right. fwd. split; [|reflexivity].
             intros H'. fwd. apply Hfpossp0.
             destr_sstate st'. inversion H'; subst.
             + eexists (_, _, _, _, _, _). eassumption.
             + exfalso. apply not. exists n. rewrite Ef. reflexivity. }
         Fail specialize (H _ eq_refl Hseqposs). (*weird error message*)
         specialize (H (execute_with_tail f s2)). cbv [execute_with_tail] in H.
         rewrite HfO in H. specialize (H eq_refl Hseqposs). destruct H as [n H].
         exists n. right. destr_sstate (f n). destruct H as [H|H].
         { destruct H as [H _]. discriminate H. }
         inversion H. subst. assumption. }
    assert (Hs1 := execute_with_tail_works' f Hfposs terminates). clear terminates.
    destruct Hs1 as [n [Hn Hs1]].
    assert (fsteps := step_until_done f n Hfposs Hn).
    exists n. destr_sstate (f n). simpl in Hn. subst. cbv [state_satisfies].
    left. split; [reflexivity|]. split.
    { enough (H' : comes_after (f n) (s1, k, t, m, l, mc) \/ f n = (s1, k, t, m, l, mc)).
      { destruct H' as [H'|H'].
        - eapply t_trans.
          2: { apply comes_after_seq. rewrite Ef in H'. apply H'. }
          apply t_step. apply seq_done_step.
        - rewrite Ef in H'. inversion H'. subst. apply t_step. apply seq_done_step. }
      rewrite <- HfO. clear -Hs1. induction n.
      - right. reflexivity.
      - left. eassert (hyp : _). 2: specialize (IHn hyp); clear hyp.
        { intros. apply Hs1. lia. }
        specialize (Hs1 n ltac:(lia)). cbv [step_state state_step execute_with_tail] in Hs1.
        destr_sstate (f n). destr_sstate (f (S n)). (*inversion Hs1; subst.
        2: { clear -H7. exfalso. induction s2; congruence. }*)
        destruct IHn as [IHn|IHn].
        + eapply t_trans.
          -- apply t_step. instantiate (1 := (_, _, _, _, _, _)). eassumption.
          -- assumption.
        + apply t_step. rewrite <- IHn. assumption. }
    intros f2 Hf2O Hf2poss.
    remember (fun m =>
                if Nat.leb m n
                then execute_with_tail f s2 m
                else f2 (m - n - 1)) as g eqn:Eg.
    specialize (H g). eassert (HgO : g O = _).
    { rewrite Eg. simpl. cbv [execute_with_tail]. rewrite HfO. reflexivity. }
    specialize (H HgO). assert (Hgposs : possible_execution g).
    { intros i. specialize (fsteps i).
      cbv [possible_execution] in Hf2poss. cbv [step_state state_step stuck_state] in *.
      subst. cbv [execute_with_tail] in *. destr_sstate (f i). destr_sstate (f (S i)).
      destruct (Nat.leb i n) eqn:Ei.
      - apply PeanoNat.Nat.leb_le in Ei. destruct (Nat.leb (S i) n) eqn:ESi.
        + apply PeanoNat.Nat.leb_le in ESi. destruct fsteps as [fdone|fsteps].
          { exfalso. specialize (Hs1 i ltac:(lia)). rewrite Ef0, Ef1 in Hs1.
            cbv [done_state] in fdone. fwd. rewrite Ef0 in fdonep0. simpl in fdonep0. subst.
            inversion Hs1. }
          left. apply seq_step. assumption.
        + apply PeanoNat.Nat.leb_nle in ESi. assert (i = n) by lia. subst.
          rewrite Ef in Ef0. inversion Ef0. subst. replace (S n - n - 1) with O by lia.
          rewrite Hf2O. left. constructor.
      - apply PeanoNat.Nat.leb_nle in Ei. destruct (Nat.leb (S i) n) eqn:ESi.
        + apply PeanoNat.Nat.leb_le in ESi. lia.
        + apply PeanoNat.Nat.leb_nle in ESi. replace (S i - n - 1) with (S (i - n - 1)) by lia.
          apply Hf2poss. }
    specialize (H Hgposs). destruct H as [b H]. exists (b - n - 1).
    rewrite Eg in H. cbv [state_satisfies execute_with_tail] in H.
    destr_sstate (f2 (b - n - 1)). destruct (Nat.leb b n).
    { exfalso. destr_sstate (f b). destruct H as [H|H].
      - destruct H as [H _]. discriminate H.
      - specialize (fsteps b). destruct fsteps as [fdone|fsteps].
        + cbv [done_state] in fdone. destruct fdone as [fdone _]. rewrite Ef1 in fdone.
          simpl in fdone. subst. inversion H. subst. inversion H1.
        + cbv [step_state state_step] in fsteps. rewrite Ef1 in fsteps.
          apply good_stuck_stuck in H. apply H. destr_sstate (f (S b)).
          eexists (_, _, _, _, _, _). apply seq_step. eassumption. }
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
      f O = (inclusion s, k, t, m, l, mc) ->
      possible_execution f ->
      satisfies f post.
  Proof.
    intros H. induction H.
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
        destr_sstate (f (S O)). inversion HSO. subst. clear HO.
        eapply satisfies_offset; eauto.
        instantiate (1 := S O). 
        eapply build_seq.
        2: apply Ef.
        2: apply possible_execution_offset; assumption.
        intros.
        eapply satisfies_weaken. 2: eapply H1; eauto.
        simpl. intros.
        specialize (H7 O). cbv [step_state stuck_state state_step] in H7.
        rewrite H6 in *. clear H6. destr_sstate (g (S O)).
        repeat match goal with
               | H: anybytes _ _ _ |- _ => clear H
               | H: map.split _ _ _ |- _ => clear H
               end.
        destruct H7 as [H7 | H7].
        -- inversion H7. subst. fwd.
           match goal with
           | A: map.split _ _ _, B: map.split _ _ _ |- _ =>
               specialize @map.split_diff with (4 := A) (5 := B) as P
           end.
           edestruct P; try typeclasses eauto.
           1: eapply anybytes_unique_domain; eassumption.
           subst. eexists (S O). left. rewrite Ef0. auto.
        -- exfalso. apply H7. clear H7. fwd. eexists (_, _, _, _, _, _).
           econstructor; eauto.
      + exists O. right. rewrite HO. econstructor; try eassumption.
        cbv [stuck_state] in HSO. rewrite HO in HSO. destruct HSO. assumption.
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
    - destruct ext_spec_ok.
      intros f HO HS. assert (HSO := HS O). destruct HSO as [HSO | HSO].
      + cbv [step_state state_step] in HSO. rewrite HO in HSO. destr_sstate (f 1%nat).
        inversion HSO. subst. unify_eval_exprs.
        specialize unique_mGive_footprint with (1 := H1) (2 := H19).
        destruct (map.split_diff unique_mGive_footprint H H6). subst.
        assert (HSSO := HS (S O)). destruct HSSO as [HSSO | HSSO].
        -- cbv [step_state state_step] in HSSO. rewrite Ef in HSSO. destr_sstate (f (S (S O))).
           inversion HSSO. subst.
           exists (S (S O)). rewrite Ef0. left. intuition.
           specialize H20 with (1 := H1). specialize H2 with (1 := H20). fwd.
           clear H unique_mGive_footprint.
           apply H2p1 in H26. unify_eval_exprs. apply H26.
        -- exists (S O). right. cbv [stuck_state] in HSSO. destruct HSSO as [HSSO _].
           rewrite Ef. econstructor.
           ++ apply H20 in H1. apply H2 in H1. fwd. eauto.
           ++ rewrite Ef in HSSO. assumption.
      + assert (step_or_not :=
                  em (exists mReceive resvals klist,
                        (*(exists m', map.split m' mKeep mReceive)map.disjoint mKeep mReceive /\*)
                          forall mid',
                            ext_spec t mGive action args mid' ->
                            mid' mReceive resvals klist)).
        destruct step_or_not as [step | not_step].
        -- fwd. assert (Hmid := step _ H1). apply H2 in Hmid. fwd.
           exfalso. apply HSO. eexists (_, _, _, _, _, _). rewrite HO.
           econstructor; eauto. eapply weaken; eauto. cbv [pointwise_relation Basics.impl]. auto.
        -- exists O. right. rewrite HO. econstructor; eauto.
           { eapply weaken. 2: eassumption. cbv [pointwise_relation Basics.impl].
             intros * Hmid. apply H2 in Hmid. fwd. eauto. }
           intros H'. apply not_step. clear not_step. fwd. cbv [state_step step_state] in H'.
           destr_sstate st'. inversion H'. subst.
           unify_eval_exprs.
           specialize unique_mGive_footprint with (1 := H1) (2 := H19).
           destruct (map.split_diff unique_mGive_footprint H H6). subst.
           assert (Hmid := H20 _ H1).
           eexists. eexists. eexists. intuition eauto. eapply H20. apply H3.
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
  
  Lemma steps_Acc'' s k t m l mc post :
    (forall (f : nat -> (scmd * _ * _ * _ * _ * _)),
        f O = (inclusion s, k, t, m, l, mc) ->
        possible_execution f ->
        satisfies f post) ->
    Acc comes_right_after (inclusion s, k, t, m, l, mc).
  Proof.
    intros.
    apply chains_finite_implies_Acc; [apply choice|].
    clear em choice.
    intros. intros H'. specialize (H f).
    simpl in H. specialize (H H0).
    assert (possible_execution f).
    { cbv [possible_execution]. intros. left. apply H'. }
    apply H in H1.
    destruct H1 as [i H1]. specialize (H' i).
    destruct (f i) as [ [ [ [ [si ki] ti] mi] li] mci].
    destruct (f (S i)) as [ [ [ [ [sSi kSi] tSi] mSi] lSi] mcSi].
    simpl in H1. simpl in H'. destruct H1 as [H1 | H1].
    - destruct H1 as [H1p1 H1p2]. subst. inversion H'.
    - remember (si, ki, ti, mi, li, mci) as st eqn:Est.
      assert (H'' : let '(s, k, t, m, l, mc) := st in
                     exists s' k' t' m' l' mc',
                       step s k t m l mc s' k' t' m' l' mc').
      { subst. do 6 eexists. eassumption. }
      clear H' Est. induction H1.
      + apply H2. clear H2. fwd. eexists (_, _, _, _, _, _). eassumption.
      + apply H4. clear H4. fwd. eexists (_, _, _, _, _, _). eassumption.
      + apply H2. clear H2. fwd. eexists (_, _, _, _, _, _). eassumption.
      + apply IHgood_stuck. clear IHgood_stuck. fwd. inversion H''; subst.
        -- do 6 eexists. eassumption.
        -- inversion H1.
  Qed.

  Search Acc.

  Lemma lift_iff {A B : Type} (f : A -> B) R x y :
    R (f x) (f y) <-> lift R f x y.
  Proof. cbv [lift]. reflexivity. Qed.

  Lemma lifted_Acc {A B : Type} (f : A -> B) R x :
    Acc R (f x) ->
    Acc (lift R f) x.
  Proof.
    intros. remember (f x) eqn:E. revert x E. induction H. intros. subst.
    constructor. intros. eapply H0.
    - eapply H1.
    - reflexivity.
  Qed.

  Lemma steps_Acc' s k t m l mc post :
    (forall (f : nat -> (scmd * _ * _ * _ * _ * _)),
        f O = (inclusion s, k, t, m, l, mc) ->
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
    (forall (f : nat -> (scmd * _ * _ * _ * _ * _)),
        f O = (inclusion s, k, t, m, l, mc) ->
        possible_execution f ->
        satisfies f post) ->
    Acc lifted_comes_after_or_repeated_prefix (s, k, t, m, l, mc).
  Proof.
    intros. apply lifted_Acc. eapply steps_Acc'; eassumption.
  Qed.

  Lemma done_stable f n :
    possible_execution f ->
    get_scmd (f n) = sskip ->
    forall m, n <= m ->
              f m = f n.
  Proof.
    intros H1 H2 H3. apply stuck_stable; try assumption. intros H'.
    destruct H' as [st' H']. destr_sstate (f n). destr_sstate st'.
    simpl in H2. rewrite H2 in H'. inversion H'.
  Qed.

  Definition successful_execution f post :=
    forall i, step_state f i \/ state_satisfies (f i) post.

  (*Lemma no_stepping_to_self :
    f O = (inclusion s, k, t, m, l, mc)*)
  
  Lemma ps_suc f post :
    possible_execution f -> satisfies f post -> successful_execution f post.
  Proof.
    intros H1 H2 n. assert (H5 := H1 n). destruct H5 as [H5|H5].
    { left. assumption. }
    right. destruct H5 as [H3 H4].
    assert (stuck_stable1 := stuck_stable _ _ H1 H3).
    destruct H2 as [m H2]. assert (H6 := satisfies_stuck _ _ H2).
    assert (stuck_stable2 := stuck_stable _ _ H1 H6).
    specialize (stuck_stable1 (Nat.max n m) ltac:(lia)).
    specialize (stuck_stable2 (Nat.max n m) ltac:(lia)).
    rewrite stuck_stable1 in stuck_stable2. rewrite stuck_stable2 in *.
    assumption.
  Qed.

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
        f O = (inclusion s, k, t, m, l, mc) ->
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
    assert (Hposs := possible_execution_exists (inclusion s, k, t, m, l, mc)).
    destruct Hposs as [f [HfO Hposs] ].
    (* it is successful and satisfies the postcondition *)
    assert (Hsatf := Hsat f HfO Hposs). assert (Hsuc := ps_suc _ _ Hposs Hsatf).
    
    destruct s.
    - econstructor. assert (Hdone := done_stable f O Hposs). rewrite HfO in Hdone.
      specialize (Hdone eq_refl). destruct Hsatf as [i Hsatf]. simpl in Hdone.
      rewrite Hdone in Hsatf by lia. destruct Hsatf as [Hsatf|Hsatf].
      2: { inversion Hsatf. }
      fwd. assumption.
    - (* the 0th state is a step state *)
      assert (HsucO := Hsuc O). destruct HsucO as [HsucO|HsucO].
      2: { rewrite HfO in HsucO. simpl in HsucO.
           destruct HsucO as [[HsucO _]|HsucO]; inversion HsucO. }
      (* find out what the 1st state is *)
      cbv [step_state state_step] in HsucO. rewrite HfO in HsucO. destr_sstate (f (S O)).
      inversion HsucO. subst.
      (* show that all states after the first state are the same as the first state *)
      assert (Hdone := done_stable f (S O) Hposs). rewrite Ef in Hdone.
      specialize (Hdone eq_refl).
      (* show that the state satisfying the postcondition is not the zeroth state *)
      destruct Hsatf as [i Hsatf]. destruct i as [|i].
      { rewrite HfO in Hsatf. destruct Hsatf as [Hsatf|Hsatf].
        - destruct Hsatf as [Hsatf _]. simpl in Hsatf. congruence.
        - inversion Hsatf. }
      (* show that the first state satisfies the postcondition *)
      rewrite Hdone in Hsatf by lia. destruct Hsatf as [Hsatf|Hsatf].
      2: { inversion Hsatf. }
      fwd. econstructor; eassumption.
    - (*this is identical to the previous case...*)
      assert (HsucO := Hsuc O). destruct HsucO as [HsucO|HsucO].
      2: { rewrite HfO in HsucO. simpl in HsucO.
           destruct HsucO as [[HsucO _]|HsucO]; inversion HsucO. }
      cbv [step_state state_step] in HsucO. rewrite HfO in HsucO. destr_sstate (f (S O)).
      inversion HsucO. subst.
      assert (Hdone := done_stable f (S O) Hposs). rewrite Ef in Hdone.
      specialize (Hdone eq_refl).
      destruct Hsatf as [i Hsatf]. destruct i as [|i].
      { rewrite HfO in Hsatf. destruct Hsatf as [Hsatf|Hsatf].
        - destruct Hsatf as [Hsatf _]. simpl in Hsatf. congruence.
        - inversion Hsatf. }
      rewrite Hdone in Hsatf by lia. destruct Hsatf as [Hsatf|Hsatf].
      2: { inversion Hsatf. }
      fwd. econstructor; eassumption.
    - (*this is identical to the previous case...*)
      assert (HsucO := Hsuc O). destruct HsucO as [HsucO|HsucO].
      2: { rewrite HfO in HsucO. simpl in HsucO.
           destruct HsucO as [[HsucO _]|HsucO]; inversion HsucO. }
      cbv [step_state state_step] in HsucO. rewrite HfO in HsucO. destr_sstate (f (S O)).
      inversion HsucO. subst.
      assert (Hdone := done_stable f (S O) Hposs). rewrite Ef in Hdone.
      specialize (Hdone eq_refl).
      destruct Hsatf as [i Hsatf]. destruct i as [|i].
      { rewrite HfO in Hsatf. destruct Hsatf as [Hsatf|Hsatf].
        - destruct Hsatf as [Hsatf _]. simpl in Hsatf. congruence.
        - inversion Hsatf. }
      rewrite Hdone in Hsatf by lia. destruct Hsatf as [Hsatf|Hsatf].
      2: { inversion Hsatf. }
      fwd. econstructor; eassumption.
    - assert (HsucO := Hsuc O). destruct HsucO as [HsucO|HsucO].
      2: { rewrite HfO in HsucO. simpl in HsucO.
           destruct HsucO as [[HsucO _]|HsucO]; inversion HsucO. subst.
           econstructor; try eassumption.
           intros. exfalso. apply H8. eexists (_, _, _, _, _, _). econstructor; eassumption. }
      cbv [step_state state_step] in HsucO. rewrite HfO in HsucO. destr_sstate (f (S O)).
      inversion HsucO. subst.
      econstructor; eauto. clear a f Ef mStack HfO Hposs Hsatf Hsuc HsucO H3 H15 H16.
      intros. eset (st2 := (_, _, _, _, _, _)).
      assert (Xs := X st2).
      eassert (lt : _). 2: specialize (Xs lt); clear lt.
      { cbv [lifted_comes_after_or_repeated_prefix lift]. simpl. eapply t_trans.
        2: { apply t_step. right. instantiate (1 := (_, _, _, _, _, _)).
             apply t_step. econstructor; eauto. }
        apply t_step. left. apply t_step. constructor. }
      simpl in Xs.
      eassert (Hind' : forall g, g O = (_, _, _, _, _, _) -> possible_execution g -> satisfies g post).
      { intros g HgO Hpossg. eset (Sg := fun n => match n with
                                                        | O => _
                                                        | S n' => g n'
                                                  end).
        specialize (Hsat Sg eq_refl). assert (Hsathyp : possible_execution Sg).
        2: specialize (Hsat Hsathyp); clear Hsathyp.
        { intros n. destruct n as [|n].
          - left. cbv [step_state state_step]. simpl. rewrite HgO. simpl.
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
      assert (Hsuc := ps_suc _ _ Hpossg' Hsat'). assert (HsucO := Hsuc O).
      destruct HsucO as [HsucO|HsucO].
      2: { rewrite HgO in HsucO. destruct HsucO as [[HsucO _]|HsucO]; inversion HsucO. }
      cbv [step_state state_step] in HsucO. rewrite HgO in HsucO. destr_sstate (g (S O)).
      inversion HsucO. subst.
      assert (Hdone := done_stable g (S O) Hpossg'). rewrite Ef in Hdone.
      specialize (Hdone eq_refl).
      destruct Hsat' as [i Hsat']. destruct i as [|i].
      { rewrite HgO in Hsat'. destruct Hsat' as [Hsat'|Hsat'].
        - destruct Hsat' as [Hsat' _]. simpl in Hsat'. congruence.
        - inversion Hsat'. }
      rewrite Hdone in Hsat' by lia. destruct Hsat' as [Hsat'|Hsat'].
      2: { inversion Hsat'. }
      destruct Hsat' as [_ Hsat']. eauto.
    - assert (HsucO := Hsuc O). destruct HsucO as [HsucO|HsucO].
      2: { rewrite HfO in HsucO. destruct HsucO as [[HsucO _]|HsucO]; inversion HsucO. }
      cbv [step_state state_step] in HsucO. rewrite HfO in HsucO. destr_sstate (f (S O)).
      inversion HsucO; subst.
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
          - left. cbv [step_state state_step]. rewrite HgO. assumption.
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
          - left. cbv [step_state state_step]. rewrite HgO. assumption.
          - specialize (Hgposs n). apply Hgposs. }
        destruct Hsat as [n Hsat]. destruct n as [|n].
        { destruct Hsat as [Hsat|Hsat].
          - destruct Hsat as [Hsat _]. simpl in Hsat. discriminate Hsat.
          - inversion Hsat. }
        exists n. apply Hsat.
    - clear f HfO Hposs Hsatf Hsuc.
      assert (Xs1 := X (s1, k, t, m, l, mc)). eassert (lt : _). 2: specialize (Xs1 lt); clear lt.
      { apply t_step. (* <- this is magic, and I do not understand it *)
        left. apply t_step. constructor. }
      simpl in Xs1. assert (Hsatinv := invert_seq). specialize Hsatinv with (1 := Hsat).
      fold inclusion in Hsatinv. specialize Xs1 with (1 := Hsatinv).
      econstructor. 1: eapply Xs1. simpl. intros * [afters2 Hs2].
      fold sstate in *.
      assert (Xs2 := X (s2, k', t', m', l', mc')). eassert (lt: _). 2: specialize (Xs2 lt); clear lt.
      { Check t_trans. cbv [lifted_comes_after_or_repeated_prefix lift]. simpl.
        apply t_step. right. eassumption. }
      simpl in Xs2. specialize Xs2 with (1 := Hs2). apply Xs2.
    - assert (HsucO := Hsuc O). destruct HsucO as [HsucO|HsucO].
      2: { rewrite HfO in HsucO. destruct HsucO as [[HsucO _]|HsucO]; inversion HsucO. }
      cbv [step_state state_step] in HsucO. rewrite HfO in HsucO. destr_sstate (f (S O)).
      inversion HsucO; subst.
      + assert (Hdone := done_stable f (S O) Hposs). rewrite Ef in Hdone.
        specialize (Hdone eq_refl).
        destruct Hsatf as [i Hsatf]. destruct i as [|i].
        { rewrite HfO in Hsatf. destruct Hsatf as [Hsatf|Hsatf].
          - destruct Hsatf as [Hsatf _]. simpl in Hsatf. congruence.
          - inversion Hsatf. }
        rewrite Hdone in Hsatf by lia. destruct Hsatf as [Hsatf|Hsatf].
        2: { inversion Hsatf. }
        fwd. eapply while_false; eassumption.
      + (*I'm kind of inlining the whole proof for the seq case here, plus some more stuff...
          I wouldn't have to do this if jump_back would just be a valid thing in the
          big-step language.  Arguably I should have some intermediate big-step language.
          Oh well. *)
        Check invert_seq.
        assert (forall g, g O = f (S O) -> possible_execution g -> satisfies g post).
        { intros. specialize (Hsat (fun n => match n with
                                             | O => f O
                                             | S n' => g n'
                                             end)).
          simpl in Hsat. rewrite HfO in Hsat. specialize (Hsat eq_refl).
          eassert (Hposs' : _). 2: specialize (Hsat Hposs'); clear Hposs'.
          { intros n. destruct n.
            - left. cbv [step_state state_step]. rewrite H. rewrite Ef. apply HsucO.
            - apply H0. (*apply continues to impress me*) }
          destruct Hsat as [n Hsat]. destruct n as [|n].
          { cbv [state_satisfies] in Hsat. destruct Hsat as [Hsat|Hsat].
            - destruct Hsat as [Hsat _]. simpl in Hsat. congruence.
            - inversion Hsat. }
          exists n. apply Hsat. }
        rewrite Ef in H. assert (H' := invert_seq). specialize H' with (1 := H).
        clear H.
        assert (Xs := X (s, leak_bool true :: k', t0, m0, l0, mc0)).
        eassert (lt : _). 2: specialize (Xs lt); clear lt.
        { cbv [lifted_comes_after_or_repeated_prefix lift]. simpl. eapply t_trans.
          2: { apply t_step. right. apply t_step. cbv [comes_right_after state_step step_state].
               instantiate (1 := (_, _, _, _, _, _)). simpl. eassumption. }
          apply t_step. left. apply t_step. constructor. }
        simpl in Xs. specialize Xs with (1 := H'). clear H'.
        eapply while_true; try eassumption. simpl. intros * [Hlt Hind]. clear Xs.
        assert (Xw := X (cmd.while test s, k'', t', m', l', ami 2 (aml 2 (amj 1 mc'')))).
        eassert (lt' : _). 2: specialize (Xw lt'); clear lt'.
        { cbv [lifted_comes_after_or_repeated_prefix lift]. simpl.
          apply t_step. right. eapply t_trans.
          2: { apply t_step. instantiate (1 := (_, _, _, _, _, _)). apply HsucO. }
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
          - left. cbv [step_state state_step]. simpl. instantiate (1 := (_, _, _, _, _, _)).
            simpl. eapply seq_step. econstructor.
          - destruct n as [|n].
            + left. cbv [step_state state_step]. simpl. rewrite HhO. constructor.
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
    - assert (HsucO := Hsuc O). destruct HsucO as [HsucO|HsucO].
      2: { rewrite HfO in HsucO. destruct HsucO as [[HsucO _]|HsucO]; inversion HsucO. }
      cbv [step_state state_step] in HsucO. rewrite HfO in HsucO. destr_sstate (f (S O)).
      inversion HsucO. subst. assert (HsucSO := Hsuc (S O)). destruct HsucSO as [HsucSO|HsucSO].
      2: { rewrite Ef in HsucSO. destruct HsucSO as [[HsucSO _]|HsucSO]; inversion HsucSO.
           subst. inversion H0. }
      cbv [step_state state_step] in HsucSO. rewrite Ef in HsucSO. destr_sstate (f (S (S O))).
      inversion HsucSO. subst. inversion H12. subst.
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
          - left. cbv [step_state state_step]. rewrite Ef. simpl. econstructor; eauto.
          - destruct n as [|n].
            + left. cbv [step_state state_step]. rewrite HgO, Ef0, Ef. constructor.
              econstructor; eassumption.
            + apply Hpossg. }
        destruct Hsat as [n Hsat]. destruct n as [|n].
        { cbv [state_satisfies] in Hsat. simpl in Hsat. destruct Hsat as [Hsat|Hsat].
          - destruct Hsat as [Hsat _]. congruence.
          - inversion Hsat. }
        destruct n as [|n].
        { cbv [state_satisfies] in Hsat. rewrite Ef in Hsat. destruct Hsat as [Hsat|Hsat].
          - destruct Hsat as [Hsat _]. congruence.
          - inversion Hsat. subst. inversion H0. }
        exists n. apply Hsat. }
      rewrite Ef0 in Hind. assert (Hind' := invert_seq). specialize Hind' with (1 := Hind).
      clear Hind.
      simpl in X. specialize X with (1 := Hind'). clear Hind'.
      econstructor; try eassumption. (*X is one assumption*)
      simpl. intros * [Hlt Hafter].
      assert (Hposs' := possible_execution_exists (end_call binds rets l0, k'', t', m', st1, mc'')).
      destruct Hposs' as [g [HgO Hgposs]].
      assert (Hsatg := Hafter g HgO Hgposs). assert (Haftersuc := ps_suc _ _ Hgposs Hsatg).
      assert (HaftersucO := Haftersuc O). destruct HaftersucO as [HaftersucO|HaftersucO].
      2: { rewrite HgO in HaftersucO. destruct HaftersucO as [[HaftersucO _]|HaftersucO]; inversion HaftersucO. }
      cbv [step_state state_step] in HaftersucO. rewrite HgO in HaftersucO. destr_sstate (g (S O)).
      inversion HaftersucO. subst.
      assert (Hdone := done_stable g (S O) Hgposs). rewrite Ef1 in Hdone.
      specialize (Hdone eq_refl).
      destruct Hsatg as [i Hsatg]. destruct i as [|i].
      { rewrite HgO in Hsatg. destruct Hsatg as [Hsatg|Hsatg].
        - destruct Hsatg as [Hsatg _]. simpl in Hsatg. congruence.
        - inversion Hsatg. }
      rewrite Hdone in Hsatg by lia. destruct Hsatg as [Hsatg|Hsatg].
      2: { inversion Hsatg. }
      fwd. eauto.
    - destruct ext_spec_ok.
      assert (HsucO := Hsuc O).
      assert (stuck_enough: good_stuck (f O) -> exec (cmd.interact binds action args) k t m l mc post).
      { clear HsucO. intros Hstuck. rewrite HfO in Hstuck. inversion Hstuck. subst.
        econstructor. 3: eapply intersect. (*not H9*) all: try eassumption.
        simpl. intros * H. exfalso. apply H10. eexists (_, _, _, _, _, _).
        econstructor; eassumption. }
      destruct HsucO as [HsucO|HsucO].
      2: { apply stuck_enough. rewrite HfO in *.
           destruct HsucO as [[HsucO _]|HsucO]; [discriminate HsucO|assumption]. }
      cbv [step_state state_step] in HsucO. rewrite HfO in HsucO. destr_sstate (f (S O)).
      inversion HsucO. subst. econstructor. 3: eapply intersect. all: try eassumption.
      rewrite HfO in stuck_enough. simpl.
      clear f HfO Hposs Hsatf Hsuc Ef mReceive resvals klist HsucO H16.
      intros * H. eset (f1 := (_, _, _, _, _, _)).
      assert (HpossSf := possible_execution_exists f1).
      destruct HpossSf as [Sf [SfO Sfposs]].
      eset (f := fun n => match n return sstate with
                            | O => _
                            | S n' => Sf n'
                            end).
        specialize (Hsat f eq_refl). assert (Hpossf : possible_execution f).
      { intros n. destruct n.
        - left. cbv [step_state state_step]. simpl. rewrite SfO. econstructor; eassumption.
        - specialize (Sfposs n). apply Sfposs. }
      specialize (Hsat Hpossf).
      assert (Hdone := done_stable f (S (S O)) Hpossf). Check ps_suc. 
      assert (Hsuc := ps_suc _ _ Hpossf Hsat). assert (HsucSO := Hsuc (S O)).
      destruct HsucSO as [HsucSO|HsucSO].
      + cbv [step_state state_step] in HsucSO. simpl in HsucSO. rewrite SfO in HsucSO.
        destr_sstate (Sf (S O)). simpl in HsucSO. inversion HsucSO. subst.
        eexists. split; eauto. intros.      
        simpl in Hdone. rewrite Ef in Hdone. specialize (Hdone eq_refl).
        destruct Hsat as [i Hsat]. destruct i as [|i].
        { simpl in Hsat. destruct Hsat as [Hsat|Hsat].
          - destruct Hsat as [Hsat _]. simpl in Hsat. congruence.
          - exfalso. inversion Hsat. subst. assert (HsucO := Hsuc O).
            destruct HsucO as [HsucO|HsucO].
            + apply H14. eexists. eapply HsucO.
            + simpl in HsucO. destruct HsucO as [[HsucO _]|HsucO]; [inversion HsucO|].
              specialize (Hpossf O). destruct Hpossf as [Hpossf|Hpossf].
              -- eapply step_not_stuck; eassumption.
              -- destruct Hpossf as [_ Hpossf]. simpl in Hpossf. rewrite SfO in Hpossf.
                 Fail congruence. discriminate Hpossf. }
        destruct i as [|i].
        { simpl in Hsat. rewrite SfO in Hsat. destruct Hsat as [Hsat|Hsat].
          - destruct Hsat as [Hsat _]. simpl in Hsat. congruence.
          - exfalso. inversion Hsat. subst. apply H18. eexists (_, _, _, _, _, _). eassumption. }
        simpl in Hsat. replace (Sf (S i)) with (f (S (S i))) in Hsat by reflexivity.
        rewrite Hdone in Hsat by lia. destruct Hsat as [Hsat|Hsat].
        2: { inversion Hsat. }
        destruct Hsat as [_ Hsat]. Search map.split.
        specialize @map.split_det with (1 := H23) (2 := H0).
        intros. subst. apply Hsat.
      + destruct HsucSO as [HsucSO|HsucSO].
        { simpl in HsucSO. rewrite SfO in HsucSO. simpl in HsucSO. destruct HsucSO. congruence. }
        simpl in HsucSO. rewrite SfO in HsucSO.
        inversion HsucSO. subst. fwd. eexists. split; eauto. intros.
        exfalso. apply H17. clear H17. eexists (_, _, _, _, _, _). econstructor; eassumption.
  Qed.
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

  Definition get_trace (st : sstate) :=
    let '(s, k, t, m, l, mc) := st in k.

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
  Proof. Admitted.

  Lemma step_extends_trace {pick_sp : PickSp} st st' :
    state_step false st st' ->
    exists k'', get_trace st' = k'' ++ get_trace st.
  Proof. Admitted.

  Lemma steps_extend_trace {pick_sp : PickSp} f n :
    (forall i, i < n -> state_step false (f i) (f (S i))) ->
    exists k'', get_trace (f n) = k'' ++ get_trace (f O).
  Proof. Admitted.
    
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

  Lemma step_states_equiv {pick_sp : PickSp} f n :
    (forall i, i < n -> step_state true f i) <->
      ((forall i, i < n -> step_state false f i) /\
         exists k'',
           get_trace (f n) = k'' ++ get_trace (f O) /\
             predicts (fun k_ => consume_word (pick_sp (rev k_ ++ get_trace (f O)))) (rev k'')).
  Proof.
    induction n.
    - split.
      + intros H. split.
        -- intros. lia.
        -- eexists; split; [trace_alignment|]. constructor.
      + intros. lia.
    - split.
      + destruct IHn as [IHn _]. intros H. eassert (hyp : _). 2: specialize (IHn hyp); clear hyp.
        { intros. apply H. lia. }
        fwd. split.
        -- intros. specialize (H i ltac:(lia)). cbv [step_state] in H.
           rewrite step_state_equiv in H. fwd. assumption.
        -- specialize (H n ltac:(lia)). cbv [step_state] in H. rewrite step_state_equiv in H.
           destruct H as [_ H]. fwd. eexists. split.
           { rewrite Hp0. rewrite IHnp1p0. trace_alignment. }
           rewrite app_nil_r. rewrite rev_app_distr. apply predicts_app.
           ++ assumption.
           ++ eapply predicts_ext. 2: eassumption. simpl. intros. f_equal. f_equal.
              rewrite rev_app_distr. rewrite rev_involutive. repeat rewrite <- app_assoc.
              rewrite IHnp1p0. reflexivity.
      + destruct IHn as [_ IHn]. intros H. fwd.
        assert (H' := steps_extend_trace f n).
        eassert (hyp : _). 2: specialize (H' hyp); clear hyp.
        { intros. apply Hp0. lia. }
        assert (extend := Hp0 n ltac:(lia)). apply step_extends_trace in extend.
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
        cbv [step_state]. rewrite step_state_equiv. fwd. split.
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
  Lemma poss_det_nondet {pick_sp : PickSp} f :
    possible_execution_det f <->
      (possible_execution_nondet f /\ forall n,
        exists k'',
          get_trace (f (S n)) = k'' ++ get_trace (f O) /\
            predicts (fun k_ => consume_word (pick_sp (rev k_ ++ get_trace (f O)))) (rev k'')).
  Proof. Abort.

  (*jLemma step_nondet_not_stuck_det {pick_sp : PickSp} f i:
    step_state false f i ->
    stuck_state true f i ->
    False.
  Proof.
    intros H1 H2.cbv [step_state stuck_state] in *. fwd. rewrite H2p1 in *. clear H2p1.
    remember (f i) as st. clear i Heqst. destr_sstate st. inversion H1; subst.
    - apply H2p0. eexists (_, _, _, _, _, _). econstructor; eauto.*)
 
  Lemma det_to_nondet {pick_sp : PickSp} s k t m l mc post :
    excluded_middle ->
    (forall (f : nat -> _),
        f O = (s, k, t, m, l, mc) ->
        possible_execution_nondet f ->
        satisfies_nondet f (fun k' t' m' l' mc' =>
                              exists k'',
                                k' = k'' ++ k /\
                                  (predicts (fun k_ => consume_word (pick_sp (rev k_ ++ k))) (List.rev k'') ->
                                   post k' t' m' l' mc'))) ->
    (forall (f : nat -> _),
        f O = (s, k, t, m, l, mc) ->
        possible_execution_det f ->
        satisfies_det f post).
  Proof.
    intros em H f HfO Hfposs. assert (nondet_or_not := em (possible_execution_nondet f)).
    destruct nondet_or_not as [nondet|not].
    - specialize (H _ ltac:(eassumption) ltac:(eassumption)). cbv [satisfies_nondet] in H.
      destruct H as [n H].
      apply (min_satisfies _ ltac:(eassumption) _ _ _ ltac:(eassumption)) in H.
      clear n. destruct H as [n [H1 H2]]. destr_sstate (f n). cbv [state_satisfies] in H1.
      destruct H1 as [H1|H1].
      + fwd.
      fwd. (*does nothing?*) destruct H1 as [? H1]. subst.
      fwd. simpl in H1. cbv [state_satisfies] in H1. fwd.
      destruct H as [n H].
      
    assert (Hfnondet : forall f, possible_execution_det f -> possible_execution_nondet f). { admit. }
    specialize (H f H0 (Hfnondet _ H1)). destruct H as [n H]. exists n.
    destr_sstate (f n).
    destruct H as [H|H].
    - fwd. assert (H' : forall f s k t m l mc s' k' t' m' l' mc', possible_execution_det f ->
                             f O = (s, k, t, m, l, mc) ->
                             f n = (s', k', t', m', l', mc') ->
                             exists k'', k' = k'' ++ k /\
                                           predicts (fun k_ => consume_word (pick_sp (rev k_ ++ k))) (rev k'')). { admit. }
      specialize H' with (1 := H1) (2 := H0) (3 := Ef). fwd. apply app_inv_tail in H'p0. subst.
      specialize Hp1p1 with (1 := H'p1). left. auto.
    - right. assert (thing : forall st, good_stuck false st -> good_stuck true st). { admit. }
      apply thing. assumption.
  Qed.

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
