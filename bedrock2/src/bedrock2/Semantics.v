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
  Context {width: Z} {BW: Bitwidth width} {word: word.word width}.
  Context {locals: map.map String.string word}.

  (* this is the expr evaluator that is used to verify execution time, the just-correctness-oriented version is below *)
  Section WithMemAndLocals.
    Context (l : locals).

    Local Notation "x <- a ; f" := (match a with Some x => f | None => None end)
      (right associativity, at level 70).

    Fixpoint eval_expr (e : expr) : option word :=
      match e with
      | expr.literal v => Some (word.of_Z v)
      | expr.var x => map.get l x
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

Require Import bedrock2.MemList.
Module multiexec. Section WithParams.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map (word * nat) byte}.
  Context {locals: map.map String.string word}.
  (* Context {ext_spec: ExtSpec}. *)
  Section WithEnv.
  Context (e: env).
  
  Definition nst := list (word * nat * mem). (*'nondeterministic state', a trace of stackalloc addrs*)
  Definition addrs := list (word * nat + locals). (* a _stack_ of stackalloc addrs *)

  Implicit Types post : (nst -> Prop) -> (nst -> addrs) -> (nst -> mem) -> (nst -> locals) -> Prop. (* COQBUG: unification finds Type instead of Prop and fails to downgrade *)
  Check ptsto. Search (_ -> Init.Byte.byte).
  Inductive exec: cmd -> (nst -> Prop) -> (nst -> addrs) -> (nst -> mem) -> (nst -> locals) ->
                  ((nst -> Prop) -> (nst -> addrs) -> (nst -> mem) -> (nst -> locals) -> Prop) -> Prop :=
  | skip: forall H A m l post,
      post H A m l ->
      exec cmd.skip H A m l post
  | set: forall x e H A m l post v,
      (forall n, H n -> eval_expr (l n) e = Some (v n)) ->
      post H A m (fun n => map.put (l n) x (v n)) ->
      exec (cmd.set x e) H A m l post
  | unset: forall x H A m l post,
      post H A m (fun n => map.remove (l n) x) ->
      exec (cmd.unset x) H A m l post
  | store: forall ea ev (H : nst -> Prop) A m mbyte mbyte' mrest l post a v v0 m',
      (forall n, H n ->
            eval_expr (l n) ea = Some (a n) /\
              eval_expr (l n) ev = Some (v n) /\
              map.split (m n) (mbyte n) (mrest n) /\
              map.split (m' n) (mbyte' n) (mrest n)) ->
      ptsto H a (fun n' => byte.of_Z (word.unsigned (word := word) (v0 n'))) mbyte ->
      ptsto H a (fun n' => byte.of_Z (word.unsigned (word := word) (v n'))) mbyte' ->
      post H A m' l ->
      exec (cmd.store access_size.one ea ev) H A m l post
  | load: forall ea ev (H : nst -> Prop) A m mbyte mrest l post a v m',
      (forall n, H n ->
            eval_expr (l n) ea = Some (a n) /\
              map.split (m n) (mbyte n) (mrest n)) ->
      ptsto H a (fun n' => byte.of_Z (word.unsigned (word := word) (v n'))) mbyte ->
      post H A m' l ->
      exec (cmd.store access_size.one ea ev) H A m l post
  | stackalloc: forall x nbytes body H A mSmall l post,
      Z.modulo nbytes (bytes_per_word width) = 0 ->
      exec body (fun n => exists a lvl mStack mCombined n' b,
                     n = (a, lvl, mStack) :: n' /\
                       mStack = map.put map.empty (a, lvl) b /\
                       map.split mCombined (mSmall n') mStack)
          (fun n =>
             match n with
             | (a, lvl, mStack) :: n' => inl (a, lvl) :: A n'
             | _ => nil
             end)
          (fun n =>
             match n with
             | (a, lvl, mStack) :: n' => map.putmany (mSmall n') mStack
             | _ => map.empty
             end)
          (fun n =>
             match n with
             | (a, lvl, mStack) :: n' => map.put (l n') x a
             | _ => map.empty
             end)
          (fun H' A' mCombined' l' =>
             exists mSmall' mStack',
               (forall n, H' n ->
                     exists a lvl b, A' n = inl (a, lvl) :: A n /\
                                  mStack' n = map.put map.empty (a, lvl) b/\
                                  map.split (mCombined' n) (mSmall' n) (mStack' n)) /\
                 post H' A mSmall' l') ->
      exec (cmd.stackalloc x nbytes body) H A mSmall l post
  | if_true_false: forall H A m l e c1 c2 post v,
      (forall n, H n ->
            eval_expr (l n) e = Some (v n)) ->
      exec c1 (fun n => word.unsigned (v n) <> 0 /\ H n) A m l post ->
      exec c2 (fun n => word.unsigned (v n) = 0 /\ H n) A m l post -> 
      exec (cmd.cond e c1 c2) H A m l post
  | seq: forall c1 c2 H A m l post mid,
      exec c1 H A m l mid ->
      (forall H' A' m' l', mid H' A' m' l' -> exec c2 H' A' m' l' post) ->
      exec (cmd.seq c1 c2) H A m l post
  | while_true_false: forall e c H A m l post mid v,
      (forall n, H n ->
            eval_expr (l n) e = Some (v n)) ->
      post (fun n => word.unsigned (v n) = 0 /\ H n) A m l ->
      exec c (fun n => word.unsigned (v n) <> 0 /\ H n) A m l mid ->
      (forall H' A' m' l', mid H' A' m' l' -> exec (cmd.while e c) H' A' m' l' post) ->
      exec (cmd.while e c) H A m l post.

  Context {word_ok: word.ok word} {mem_ok: map.ok mem}.

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
