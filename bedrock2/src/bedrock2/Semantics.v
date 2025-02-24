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

Module multiexec. Section WithParams.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word byte}.
  Context {locals: map.map String.string word}.
  Context {ext_spec: ExtSpec}.
  Section WithEnv.
  Context (e: env).

  Definition nst := list (word * mem). (*'nondeterministic state', a trace of stackalloc addrs*)
  Definition addrs := list (word + locals). (* a _stack_ of stackalloc addrs *)

  Implicit Types post : (nst -> Prop) -> (nst -> addrs) -> (nst -> trace) -> (nst -> mem) -> (nst -> locals) -> Prop. (* COQBUG: unification finds Type instead of Prop and fails to downgrade *)
  Inductive exec: cmd -> (nst -> Prop) -> (nst -> addrs) -> (nst -> trace) -> (nst -> mem) -> (nst -> locals) ->
                  ((nst -> Prop) -> (nst -> addrs) -> (nst -> trace) -> (nst -> mem) -> (nst -> locals) -> Prop) -> Prop :=
  | skip: forall H A t m l post,
      post H A t m l ->
      exec cmd.skip H A t m l post
  | set: forall x e H A t m l post v,
      (forall n, H n -> eval_expr (m n) (l n) e = Some (v n)) ->
      post H A t m (fun n => map.put (l n) x (v n)) ->
      exec (cmd.set x e) H A t m l post
  | unset: forall x H A t m l post,
      post H A t m (fun n => map.remove (l n) x) ->
      exec (cmd.unset x) H A t m l post
  | store: forall sz ea ev H A t m l post a v m',
      (forall n, H n ->
            eval_expr (m n) (l n) ea = Some (a n) /\
              eval_expr (m n) (l n) ev = Some (v n) /\
              store sz (m n) (a n) (v n) = Some (m' n)) ->
      post H A t m' l ->
      exec (cmd.store sz ea ev) H A t m l post
  | stackalloc: forall x nbytes body H A t mSmall l post,
      Z.modulo nbytes (bytes_per_word width) = 0 ->
      exec body (fun n => exists a mStack mCombined n',
                       n = (a, mStack) :: n' /\
                         anybytes a nbytes mStack /\
                         map.split mCombined (mSmall n') mStack)
          (fun n =>
             match n with
             | (a, mStack) :: n' => inl a :: A n'
             | _ => nil
             end)
          (fun n =>
             match n with
             | (a, mStack) :: n' => t n'
             | _ => nil
             end)
          (fun n =>
             match n with
             | (a, mStack) :: n' => map.putmany (mSmall n') mStack
             | _ => map.empty
             end)
          (fun n =>
             match n with
             | (a, mStack) :: n' => map.put (l n') x a
             | _ => map.empty
             end)
          (fun H' A' t' mCombined' l' =>
             exists mSmall' mStack',
               (forall n, H' n ->
                     exists a, A' n = inl a :: A n /\
                     anybytes a nbytes (mStack' n) /\
                       map.split (mCombined' n) (mSmall' n) (mStack' n)) /\
                 post H' A t' mSmall' l') ->
      exec (cmd.stackalloc x nbytes body) H A t mSmall l post
  | if_true_false: forall H A t m l e c1 c2 post v,
      (forall n, H n ->
            eval_expr (m n) (l n) e = Some (v n)) ->
      exec c1 (fun n => word.unsigned (v n) <> 0 /\ H n) A t m l post ->
      exec c2 (fun n => word.unsigned (v n) = 0 /\ H n) A t m l post -> 
      exec (cmd.cond e c1 c2) H A t m l post
  | seq: forall c1 c2 H A t m l post mid,
      exec c1 H A t m l mid ->
      (forall H' A' t' m' l', mid H' A' t' m' l' -> exec c2 H' A' t' m' l' post) ->
      exec (cmd.seq c1 c2) H A t m l post
  | while_true_false: forall e c H A t m l post mid v,
      (forall n, H n ->
            eval_expr (m n) (l n) e = Some (v n)) ->
      post (fun n => word.unsigned (v n) = 0 /\ H n) A t m l ->
      exec c (fun n => word.unsigned (v n) <> 0 /\ H n) A t m l mid ->
      (forall H' A' t' m' l', mid H' A' t' m' l' -> exec (cmd.while e c) H' A' t' m' l' post) ->
      exec (cmd.while e c) H A t m l post
  | call: forall binds fname arges H A t m l post params rets fbody args lf mid,
      (forall n, H n ->
            map.get e fname = Some (params, rets, fbody) /\
            eval_call_args (m n) (l n) arges = Some (args n) /\
            map.of_list_zip params (args n) = Some (lf n)) ->
      exec fbody H (fun n => inr (l n) :: A n) t m lf mid ->
      (forall H' A' t' m' st1,
          mid H' A' t' m' st1 ->
          exists l',
            (forall n, H' n ->
                  exists l0,
                    A' n = inr l0 :: A n /\
                  exists retvs, map.getmany_of_list (st1 n) rets = Some (retvs n) /\
                             map.putmany_of_list_zip binds (retvs n) l0 = Some (l' n)) /\
              post H' A t' m' l') ->
      exec (cmd.call binds fname arges) H A t m l post
  | interact: forall binds action arges args H A t m l post mKeep mGive mid,
      (forall n, H n ->
            map.split (m n) (mKeep n) (mGive n) /\
            eval_call_args (m n) (l n) arges = Some (args n) /\
              ext_spec (t n) (mGive n) action (args n) (mid n)) ->
      (*this is a bit weird.  when given mReceive and resvals that are valid (according to ext_spec), this requires (as you'd expect) that every state of the multistate behaves as it's required to.  but interestingly, when given mReceive and resvals that are partially valid, it requires the states for which they're valid to behave as they're required to.  so we get 'partially vacuous' behaviour.  of course this has no practical relevance, since we only care about valid mReceive and resvals, and it's not any extra effort to prove the partly-correct hing.*)
      (forall mReceive resvals,
          exists m' l',
            (forall n, H n ->
                  mid n (mReceive n) (resvals n) ->
                  map.putmany_of_list_zip binds (resvals n) (l n) = Some (l' n) /\
                    map.split (m' n) (mKeep n) (mReceive n)) /\
            post H A (fun n => cons ((mGive n, action, args n), (mReceive n, resvals n)) (t n)) m' l') ->
      exec (cmd.interact binds action arges) H A t m l post.

  Context {word_ok: word.ok word} {mem_ok: map.ok mem} {ext_spec_ok: ext_spec.ok ext_spec}.

  Lemma seq_cps: forall c1 c2 H A t m l post,
      exec c1 H A t m l (fun H' A' t' m' l' => exec c2 H' A' t' m' l' post) ->
      exec (cmd.seq c1 c2) H A t m l post.
  Proof. intros. eauto using seq. Qed.

  Lemma weaken: forall s H A t m l post1,
      exec s H A t m l post1 ->
      forall post2,
        (forall H' A' t' m' l', post1 H' A' t' m' l' -> post2 H' A' t' m' l') ->
        exec s H A t m l post2.
  Proof.
    induction 1; intros; try solve [econstructor; eauto].
    - eapply stackalloc. 1: assumption.
      intros.
      eapply IHexec; eauto.
      intros. fwd. do 2 eexists. split; [|solve[eauto]].
      intros. specialize H3p0 with (1 := H3). fwd. eauto.
    - eapply call.
      2: eapply IHexec.
      all: eauto.
      intros.
      apply H2 in H4. fwd. eexists. split; [|eauto]. intros. apply H4p0 in H4.
      fwd. eauto.
    - econstructor; eauto. intros. specialize (H1 mReceive resvals).
      fwd. eauto.
  Qed.

  (* should be trivial, but i dont feel like doing it now *)
  
  (* Lemma intersect: forall t l m s post1, *)
  (*     exec s t m l post1 -> *)
  (*     forall post2, *)
  (*       exec s t m l post2 -> *)
  (*       exec s t m l (fun t' m' l' => post1 t' m' l' /\ post2 t' m' l'). *)
  (* Proof. *)
  (*   induction 1; *)
  (*     intros; *)
  (*     match goal with *)
  (*     | H: exec _ _ _ _ _ |- _ => inversion H; subst; clear H *)
  (*     end; *)
  (*     try match goal with *)
  (*     | H1: ?e = Some (?x1, ?y1, ?z1), H2: ?e = Some (?x2, ?y2, ?z2) |- _ => *)
  (*       replace x2 with x1 in * by congruence; *)
  (*         replace y2 with y1 in * by congruence; *)
  (*         replace z2 with z1 in * by congruence; *)
  (*         clear x2 y2 z2 H2 *)
  (*     end; *)
  (*     repeat match goal with *)
  (*            | H1: ?e = Some ?v1, H2: ?e = Some ?v2 |- _ => *)
  (*              replace v2 with v1 in * by congruence; clear H2 *)
  (*            end; *)
  (*     repeat match goal with *)
  (*            | H1: ?e = Some ?v1, H2: ?e = Some ?v2 |- _ => *)
  (*              replace v2 with v1 in * by congruence; clear H2 *)
  (*            end; *)
  (*     try solve [econstructor; eauto | exfalso; congruence]. *)

  (*   - econstructor. 1: eassumption. *)
  (*     intros. *)
  (*     rename H0 into Ex1, H11 into Ex2. *)
  (*     eapply weaken. 1: eapply H1. 1,2: eassumption. *)
  (*     1: eapply Ex2. 1,2: eassumption. *)
  (*     cbv beta. *)
  (*     intros. fwd. *)
  (*     lazymatch goal with *)
  (*     | A: map.split _ _ _, B: map.split _ _ _ |- _ => *)
  (*       specialize @map.split_diff with (4 := A) (5 := B) as P *)
  (*     end. *)
  (*     edestruct P; try typeclasses eauto. 2: subst; eauto 10. *)
  (*     eapply anybytes_unique_domain; eassumption. *)
  (*   - econstructor. *)
  (*     + eapply IHexec. exact H5. (* not H *) *)
  (*     + simpl. intros *. intros [? ?]. eauto. *)
  (*   - eapply while_true. 1, 2: eassumption. *)
  (*     + eapply IHexec. exact H9. (* not H1 *) *)
  (*     + simpl. intros *. intros [? ?]. eauto. *)
  (*   - eapply call. 1, 2, 3: eassumption. *)
  (*     + eapply IHexec. exact H15. (* not H2 *) *)
  (*     + simpl. intros *. intros [? ?]. *)
  (*       edestruct H3 as (? & ? & ? & ? & ?); [eassumption|]. *)
  (*       edestruct H16 as (? & ? & ? & ? & ?); [eassumption|]. *)
  (*       repeat match goal with *)
  (*              | H1: ?e = Some ?v1, H2: ?e = Some ?v2 |- _ => *)
  (*                replace v2 with v1 in * by congruence; clear H2 *)
  (*              end. *)
  (*       eauto 10. *)
  (*   - pose proof ext_spec.mGive_unique as P. *)
  (*     specialize P with (1 := H) (2 := H7) (3 := H1) (4 := H13). *)
  (*     subst mGive0. *)
  (*     destruct (map.split_diff (map.same_domain_refl mGive) H H7) as (? & _). *)
  (*     subst mKeep0. *)
  (*     eapply interact. 1,2: eassumption. *)
  (*     + eapply ext_spec.intersect; [ exact H1 | exact H13 ]. *)
  (*     + simpl. intros *. intros [? ?]. *)
  (*       edestruct H2 as (? & ? & ?); [eassumption|]. *)
  (*       edestruct H14 as (? & ? & ?); [eassumption|]. *)
  (*       repeat match goal with *)
  (*              | H1: ?e = Some ?v1, H2: ?e = Some ?v2 |- _ => *)
  (*                replace v2 with v1 in * by congruence; clear H2 *)
  (*              end. *)
  (*       eauto 10. *)
  (* Qed. *)

  End WithEnv.
  End WithParams.
End multiexec. Notation multiexec := multiexec.exec.

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

  End WithEnv.
  End WithParams.
End exec. Notation exec := exec.exec.

Section WithParams.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word byte}.
  Context {locals: map.map String.string word}.
  Context {ext_spec: ExtSpec}.

  Check multiexec.
  Lemma exec_implies_multiexec e c t m l post :
    exec e c t m l post ->
    multiexec e c (eq nil) (fun _ => nil) (fun _ => t) (fun _ => m) (fun _ => l)
      (fun H' _ t' m' l' => forall n, H' n -> post (t' n) (m' n) (l' n)).
  Proof.
    intros H. induction H.
    - econstructor. auto.
    - econstructor; intros; subst.
      + rewrite H. f_equal. instantiate (1 := fun _ => _). reflexivity.
      + assumption.
    - econstructor. auto.
    - econstructor.
      + instantiate (1 := fun _ => _). instantiate (2 := fun _ => _). instantiate (3 := fun _ => _).
        simpl. eauto.
      + simpl. auto.
    - (*the IH will be useless here, since the eq nil will go away*)
      econstructor; auto.
      (*indeed it is useless*)
    (*to get around this, i'd need to do induction on multiple execs at a time...
      i.e. i'd need to use the same strategy as with the forall_into_inductive thing*)
  Abort.

  Lemma multiexec_implies_exec e c H A t m l post :
    multiexec e c H A t m l post ->
    forall post0,
      (forall H0 A0 t0 m0 l0, post H0 A0 t0 m0 l0 -> post0 H0 A0 t0 m0 l0) ->
    (*don't really need this much generality...*)
    (forall H' H'0 A' A'0 t' t'0 m' m'0 l' l'0,
        (forall n, H'0 n -> H' n) ->
        (forall n, H'0 n -> A'0 n = A' n /\ t'0 n = t' n /\ m'0 n = m' n /\ l'0 n = l' n) ->
        post0 H' A' t' m' l' -> post0 H'0 A'0 t'0 m'0 l'0) ->
    (*the condition on the postcondition is really quite reasonable;
      for instance, it's satisfied by any postcondition of the form
      forall n, H n -> P (t n) (m n) (l n)*)
    forall n,
      H n ->
      exec e c (t n) (m n) (l n) (fun t' m' l' =>
                                    (*the appending postcondition feels horribly hacky somehow*)
                                    exists n',
                                      post0 (eq (n' ++ n)) (fun n => A (skipn (length n') n)) (fun _ => t') (fun _ => m') (fun _ => l')).
  Proof.
    intros Hmexec. induction Hmexec; intros post0 post_to_post0 Hpost0; try match goal with | H: _ |- _ => specialize Hpost with (3 := H) end; intros; try solve [econstructor; try (exists nil); match goal with | H : _ |- _ => apply post_to_post0 in H; specialize Hpost0 with (3 := H) end; apply Hpost0; intros; subst; eauto].
    - specialize H0 with (1 := H2). fwd. econstructor; eauto. exists nil. eapply Hpost0; intros; subst; simpl; eauto. cbv beta. auto.
    - specialize H0 with (1 := H2). fwd. econstructor; eauto. exists nil. eapply Hpost0; intros; subst; simpl; eauto.
    - specialize (IHHmexec (fun H0 A0 t0 m0 l0 => exists mSmall' mStack' : multiexec.nst -> mem,
                                (forall n : multiexec.nst,
                                    H0 n ->
                                    exists a : word,
                                      A0 n = inl a :: A n /\
                                        anybytes a nbytes (mStack' n) /\ map.split (m0 n) (mSmall' n) (mStack' n)) /\
                                  post0 H0 A t0 mSmall' l0)).
      eassert _ as blah. 2: specialize (IHHmexec blah); clear blah.
      { simpl. intros. fwd. eauto. }
      eassert _ as blah. 2: specialize (IHHmexec blah); clear blah.
      { simpl. intros. fwd. do 2 eexists. split.
        - intros. specialize H2 with (1 := H4). specialize H4p0 with (1 := H2).
          specialize H3 with (1 := H4).
          fwd. eexists. rewrite H3p0. split; [eassumption|].
          split; [eassumption|]. rewrite H3p2. eassumption.
        - specialize Hpost0 with (3 := H4p1). apply Hpost0; auto. intros.
          specialize H3 with (1 := H4). fwd. auto. }
      econstructor; eauto. intros.
      specialize (IHHmexec ((a, mStack) :: n)). simpl in IHHmexec.
      specialize (IHHmexec ltac:(eauto 10)).
      destruct H3 as [H3 H4]. subst. eapply exec.weaken. 1: exact IHHmexec.
      simpl. intros. fwd. specialize (H3p0 _ eq_refl). fwd. Search skipn.
      rewrite List.skipn_app_r in E by reflexivity. injection E. intros. subst.
      eexists (mSmall' _), (mStack' _). intuition eauto. eexists.
      specialize Hpost0 with (3 := H3p1). apply Hpost0; auto.
      { intros. Search (_ ++ _ :: _ = _ ++ _ ++ _). replace (n' ++ (a0, r0) :: l0) with (n' ++ (cons (a0, r0) nil) ++ l0) by reflexivity.
        rewrite app_assoc. apply H5. }
      intros. subst. rewrite List.skipn_app_r by reflexivity.
      rewrite <- app_assoc. simpl. auto.
    - specialize (IHHmexec1 ltac:(auto)). specialize (IHHmexec2 ltac:(auto)).
      destruct (Z.eqb (word.unsigned (v n)) 0) eqn:E.
      + Search Z.eqb. apply BinInt.Z.eqb_eq in E. eapply exec.if_false; eauto.
      + apply BinInt.Z.eqb_neq in E. eapply exec.if_true; eauto.
    - specialize (IHHmexec _ (fun _ _ _ _ _ p => (H1 _ _ _ _ _ p))).
      eassert _ as blah. 2: specialize (IHHmexec blah); clear blah.
      { simpl. intros. Search t'0. specialize H4 with (1 := H8). move H4 at bottom.
        fwd. rewrite H4p1, H4p2, H4p3. specialize (H5 post1 H6). eapply exec.weaken.
        { apply H5; auto. }
        simpl. intros. fwd. eexists. specialize H7 with (3 := H4). apply H7; eauto.
        intros. subst. rewrite List.skipn_app_r by reflexivity. auto. }
      econstructor.
      { apply IHHmexec. assumption. }
      clear IHHmexec. simpl. intros. fwd. specialize (H3 post0 ltac:(assumption)).
      specialize (H3 ltac:(auto) _ eq_refl). eapply exec.weaken. 1: exact H3.
      simpl. intros. fwd. eexists. specialize Hpost0 with (3 := H4).
      apply Hpost0; eauto.
      + intros. rewrite app_assoc. eassumption.
      + intros. subst. rewrite List.skipn_app_r by reflexivity.
        rewrite <- app_assoc. do 2 rewrite List.skipn_app_r by reflexivity.
        auto.
    - specialize (IHHmexec _ (fun _ _ _ _ _ p => (H3 _ _ _ _ _ p))).
      eassert _ as blah. 2: specialize (IHHmexec blah); clear blah.
      { simpl. intros. Search t'0. specialize H6 with (1 := H10). move H6 at bottom.
        fwd. rewrite H6p1, H6p2, H6p3. specialize (H7 post1 H8). eapply exec.weaken.
        { auto. }
        simpl. intros. fwd. eexists. specialize H9 with (3 := H6). apply H9; eauto.
        intros. subst. rewrite List.skipn_app_r by reflexivity. auto. }
      destruct (Z.eqb (word.unsigned (v n)) 0) eqn:E.
      + apply BinInt.Z.eqb_eq in E. eapply exec.while_false; eauto. Check H1.
        specialize post_to_post0 with (1 := H1).
        specialize Hpost0 with (3 := post_to_post0).
        exists nil. apply Hpost0; eauto.
        -- intros. subst. simpl. auto.
        -- intros. subst. simpl. auto.
      + apply BinInt.Z.eqb_neq in E. eapply exec.while_true; eauto. simpl.
        intros. fwd. specialize (H5 post0 post_to_post0 Hpost0 _ eq_refl).
        eapply exec.weaken. 1: exact H5. simpl. intros. fwd. eexists.
        specialize Hpost0 with (3 := H6). apply Hpost0; auto.
        -- intros. subst. rewrite app_assoc. reflexivity.
        -- intros. subst. rewrite List.skipn_app_r by reflexivity.
           rewrite <- app_assoc. do 2 rewrite List.skipn_app_r by reflexivity. auto.
    - move H0 at bottom. specialize H0 with (1 := H2). fwd.
      specialize (IHHmexec (fun H' A' t' m' st1 => exists l' : multiexec.nst -> locals,
      (forall n : multiexec.nst,
       H' n ->
       exists l0 : locals,
         A' n = inr l0 :: A n /\
         (exists retvs : multiexec.nst -> list word,
            map.getmany_of_list (st1 n) rets = Some (retvs n) /\
            map.putmany_of_list_zip binds (retvs n) l0 = Some (l' n))) /\
      post0 H' A t' m' l')).
      eassert _ as blah. 2: specialize (IHHmexec blah); clear blah.
      { simpl. intros. Search mid. apply H1 in H3. fwd. eexists. split.
        - eauto.
        - apply post_to_post0. assumption.
      } 
      econstructor; eauto.
      { eapply IHHmexec; eauto. intros. fwd. eexists. split.
        - intros. specialize H0 with (1 := H4). specialize H4p0 with (1 := H0).
          fwd. specialize H3 with (1 := H4). fwd. rewrite H3p0, H3p3. eauto.
        - specialize Hpost0 with (3 := H4p1). eapply Hpost0; auto.
          intros. specialize H3 with (1 := H4). fwd. rewrite H3p1, H3p2.
          auto. }
      simpl. intros. fwd. specialize (H0p3 _ eq_refl). fwd. eexists. intuition eauto.
      rewrite List.skipn_app_r in H0p3p1p1 by reflexivity.
      eexists. intuition eauto. eexists.
      specialize Hpost0 with (3 := H0p4). apply Hpost0; eauto.
      intros. subst. rewrite List.skipn_app_r by reflexivity.
      rewrite List.skipn_app_r in H0 by reflexivity. auto.
    - intros. Search mid. move H1 at bottom. move H0 at bottom.
      specialize (H0 _ ltac:(eassumption)). fwd. econstructor; eauto.
      intros.
      specialize (H1 (fun _ => mReceive) (fun _ => resvals)).
      fwd. specialize (H1p0 _ ltac:(eassumption) ltac:(assumption)).
      fwd. eexists. intuition eauto. eexists.
      specialize post_to_post0 with (1 := H1p1).
      specialize Hpost0 with (3 := post_to_post0).
      apply Hpost0; auto.
      + intros. subst. instantiate (1 := nil). assumption.
      + intros. subst. simpl. destruct H1. destruct H1p0p1. subst. auto.
  Qed.
