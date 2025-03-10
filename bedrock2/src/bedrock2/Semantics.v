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

  Inductive mids_and_post :=
  | postcond (post: forall (q: bool) (t : trace) (m : mem) (l : locals), Prop)
  | and_then
      (first_this_happens : forall (q: bool) (t: trace) (m : mem) (l : locals), Prop)
      (and_then_later_this_happens : forall (q : bool) (t: trace) (m : mem) (l : locals), forall (idx: nat), mids_and_post).

  Record state := { q: bool; t: trace; m: mem; l: locals }.
  Definition appl_to_state {T: Type} (f : _ -> _ -> _ -> _ -> T) st := f st.(q) st.(t) st.(m) st.(l).
  Definition state_satisfies (st: state) (post: _ -> _ -> _ -> _ -> Prop) :=
    appl_to_state post st.
  
  (*this fixpoint answers the question: when does an exectution
    (infinite sequence of states) satisfy a postcondition?*)
  (*this isn't actually used anywhere for now.  it is mainly documentation.*)
  Fixpoint interp_mids_and_post (P : mids_and_post) : (nat -> state) -> Prop :=
    fun f =>
      match P with
      | postcond post => exists n, state_satisfies (f n) post
      | and_then noww later => exists n, state_satisfies (f n) noww /\
                                     let later := appl_to_state later (f n) in
                                     forall m,
                                       interp_mids_and_post (later m) f
      end.

  (*suffix_good says, given a state after prefix stuff finishes executing, whether the given postcondition holds*)
  (*idk how to explain what this fixpoint does without reference to seq.*)
  (*preconditions:
    - s1 satisfies `prefix`
    - forall q t m l post', if suffix_good q t m l post' is inhabited, then
      executing state s2 starting from state (q,t,m,l) will satisfy post'
   postcondition:
    - if return value (a Prop) is inhabited, then (seq s1 s2) satisfies `whole`
   *)
  Fixpoint sat (prefix: mids_and_post) (suffix_good: bool -> trace -> mem -> locals -> mids_and_post -> Prop) (whole : mids_and_post) : Prop :=
    match prefix, whole with
    | postcond post, _ => (forall q t m l, post q t m l -> suffix_good q t m l whole)
    | and_then mid1 prefix', and_then mid2 whole' =>
        (forall q t m l, mid1 q t m l -> mid2 q t m l) /\
          (forall q t m l n, sat (prefix' q t m l n) suffix_good (whole' q t m l n))
    | _, _ => False
    end.
  
  Inductive exec: cmd -> bool -> trace -> mem -> locals -> mids_and_post -> Prop :=
  | skip: forall t m l post,
      post true t m l ->
      exec cmd.skip true t m l (postcond post)
  | set: forall x e t m l post v,
      eval_expr m l e = Some v ->
      post true t m (map.put l x v) ->
      exec (cmd.set x e) true t m l (postcond post)
  | unset: forall x t m l post,
      post true t m (map.remove l x) ->
      exec (cmd.unset x) true t m l (postcond post)
  | store: forall sz ea ev t m l post a v m',
      eval_expr m l ea = Some a ->
      eval_expr m l ev = Some v ->
      store sz m a v = Some m' ->
      post true t m' l ->
      exec (cmd.store sz ea ev) true t m l (postcond post)
  | seq: forall c1 c2 t m l prefix post mid,
      exec c1 true t m l prefix ->
      (forall q' t' m' l' post', mid q' t' m' l' post' -> exec c2 q' t' m' l' post') ->
      sat prefix mid post ->
      exec (cmd.seq c1 c2) true t m l post
  | while_true: forall e c t m l v prefix post mid,
      eval_expr m l e = Some v ->
      word.unsigned v <> 0 ->
      exec c true t m l prefix ->
      (forall q' t' m' l' post', mid q' t' m' l' post' -> exec (cmd.while e c) q' t' m' l' post') ->
      sat prefix mid post ->
      exec (cmd.while e c) true t m l post
  | while_false: forall e c t m l post v,
      eval_expr m l e = Some v ->
      word.unsigned v = 0 ->
      post true t m l ->
      exec (cmd.while e c) true t m l (postcond post)
  | stackalloc: forall x n body t mSmall l post,
      Z.modulo n (bytes_per_word width) = 0 ->
      (forall a mStack mCombined,
        anybytes a n mStack ->
        map.split mCombined mSmall mStack ->
        exists prefix,
        exec body true t mCombined (map.put l x a) prefix /\
        sat
          prefix
          (fun q' t' mCombined' l' suffix =>
             exists post', suffix = postcond post' /\
                        exists mSmall' mStack',
                          anybytes a n mStack' /\
                            map.split mCombined' mSmall' mStack' /\
                            post' q' t' mSmall' l')
          post) ->
      exec (cmd.stackalloc x n body) true t mSmall l post
  (* | if_true: forall t m l e c1 c2 post v, *)
  (*     eval_expr m l e = Some v -> *)
  (*     word.unsigned v <> 0 -> *)
  (*     exec c1 true t m l post -> *)
  (*     exec (cmd.cond e c1 c2) true t m l post *)
  (* | if_false: forall e c1 c2 t m l post v, *)
  (*     eval_expr m l e = Some v -> *)
  (*     word.unsigned v = 0 -> *)
  (*     exec c2 true t m l post -> *)
  (*     exec (cmd.cond e c1 c2) true t m l post *)
  (* | call: forall binds fname arges t m l post params rets fbody args lf mid, *)
  (*     map.get e fname = Some (params, rets, fbody) -> *)
  (*     eval_call_args m l arges = Some args -> *)
  (*     map.of_list_zip params args = Some lf -> *)
  (*     exec fbody true t m lf mid -> *)
  (*     (forall q' t' m' st1, mid q' t' m' st1 -> *)
  (*         exists retvs, map.getmany_of_list st1 rets = Some retvs /\ *)
  (*         exists l', map.putmany_of_list_zip binds retvs l = Some l' /\ *)
  (*         post q' t' m' l') -> *)
  (*     exec (cmd.call binds fname arges) true t m l post *)
  | interact: forall binds action arges args t m l post mKeep mGive mid,
      map.split m mKeep mGive ->
      eval_call_args m l arges = Some args ->
      ext_spec t mGive action args mid ->
      (forall mReceive resvals, mid mReceive resvals ->
          exists l', map.putmany_of_list_zip binds resvals l = Some l' /\
          forall m', map.split m' mKeep mReceive ->
          post true (cons ((mGive, action, args), (mReceive, resvals)) t) m' l') ->
      exec (cmd.interact binds action arges) true t m l (postcond post)
  | quit: forall c q t m l post,
      post false t m l ->
      exec c q t m l (postcond post)
  | mid: forall c q t m l mid post,
      mid q t m l ->
      (*the quantifier here slipped past the nondeterminism! this is the whole point*)
      (forall n, exec c q t m l (post q t m l n)) ->
      exec c q t m l (and_then mid post).

  Lemma seq_cps_sorta c1 c2 t m l prefix post :
    exec c1 true t m l prefix ->
    sat prefix (exec c2) post ->
    exec (cmd.seq c1 c2) true t m l post.
  Proof.
    intros. eapply seq with (mid := exec c2). 1: eassumption. 1: auto. 1: assumption.
  Qed.

  Lemma seq_cps_for_real c1 c2 t m l post :
    exec c1 true t m l
      (postcond (fun q' t' m' l' =>
                   exec c2 q' t' m' l' post)) ->
    exec (cmd.seq c1 c2) true t m l post.
  Proof. intros. eapply seq_cps_sorta. 1: apply H. simpl. auto. Qed.

  Lemma while_true_cps_sorta ee c t m l v prefix post :
      eval_expr m l ee = Some v ->
      word.unsigned v <> 0 ->
      exec c true t m l prefix ->
      sat prefix (exec (cmd.while ee c)) post ->
      exec (cmd.while ee c) true t m l post.
  Proof. intros. eapply while_true with (mid := exec _); eauto. Qed.

  Open Scope string_scope.
  Require Import Strings.String.
  Definition ex := cmd.seq (cmd.set "x"%string (expr.literal 0)) (cmd.seq (cmd.set "x" (expr.literal 1)) (cmd.seq (cmd.set "x" (expr.literal 2)) cmd.skip)).

  Context {locals_ok: map.ok locals} {word_ok: word.ok word} {mem_ok: map.ok mem} {ext_spec_ok: ext_spec.ok ext_spec}.

  Lemma ex_works t m l : exec ex true t m l (and_then (fun _ _ _ l => map.get l "x" = Some (word.of_Z 0)) (fun _ _ _ _ _ => and_then (fun _ _ _ l => map.get l "x" = (Some (word.of_Z 1))) (fun _ _ _ _ _ => and_then (fun _ _ _ l => map.get l "x" = (Some (word.of_Z 2))) (fun _ _ _ _ _ => postcond (fun q _ _ _ => q = true))))).
  Proof.
    eapply seq_cps_sorta.
    { eapply set. 1: reflexivity. instantiate (1 := fun q' t' m' l' => q' = true /\ map.get l' "x" = Some (word.of_Z 0)). simpl. rewrite map.get_put_same. auto. }
    simpl. intros. fwd. eapply mid.
    { assumption. }
    intros _. eapply seq_cps_sorta.
    { eapply set. 1: reflexivity. instantiate (1 := fun q' t' m' l' => q' = true /\ map.get l' "x" = Some (word.of_Z 1)). simpl. rewrite map.get_put_same. auto. }
    simpl. intros. fwd. eapply mid.
    { assumption. }
    intros _. eapply seq_cps_sorta.
    { eapply set. 1: reflexivity. instantiate (1 := fun q' t' m' l' => q' = true /\ map.get l' "x" = Some (word.of_Z 2)). simpl. rewrite map.get_put_same. auto. }
    simpl. intros. fwd. eapply mid.
    { assumption. }
    intros _. apply skip. reflexivity.
  Qed.
  
  Lemma interact_cps: forall binds action arges args t m l post mKeep mGive,
      map.split m mKeep mGive ->
      eval_call_args m l arges = Some args ->
      ext_spec t mGive action args (fun mReceive resvals =>
          exists l', map.putmany_of_list_zip binds resvals l = Some l' /\
          forall m', map.split m' mKeep mReceive ->
          post true (cons ((mGive, action, args), (mReceive, resvals)) t) m' l') ->
      exec (cmd.interact binds action arges) true t m l (postcond post).
  Proof. intros. eauto using interact. Qed.
  
  (* Lemma seq_cps: forall c1 c2 t m l post, *)
  (*     exec c1 true t m l (fun q' t' m' l' => exec c2 q' t' m' l' post) -> *)
  (*     exec (cmd.seq c1 c2) true t m l post. *)
  (* Proof. intros. eauto using seq. Qed. *)

  (*could be cleverer about this... seems unnecessary though*)
  Fixpoint implies (post1 post2 : mids_and_post) :=
    match post1, post2 with
    | and_then mid1 post1', and_then mid2 post2' =>
        (forall q' t' m' l', mid1 q' t' m' l' -> mid2 q' t' m' l') /\
          (forall q' t' m' l' n, implies (post1' q' t' m' l' n) (post2' q' t' m' l' n))
    | postcond post1', postcond post2' => forall q' t' m' l', post1' q' t' m' l' -> post2' q' t' m' l'
    | _, _ => False
    end.

  Lemma weaken_sat post1 suffix_good1 suffix_good2 mid :
    (forall q t m l post1 post2, implies post1 post2 -> suffix_good1 q t m l post1 -> suffix_good2 q t m l post2) ->
    sat mid suffix_good1 post1 ->
    forall post2,
    implies post1 post2 ->
    sat mid suffix_good2 post2.
  Proof.
    intros. revert post1 post2 H0 H1. induction mid; intros.
    - destruct post1; simpl in H0; destruct post2; simpl in H1; try solve [destruct H1].
      + simpl. intros. apply H with (post1 := postcond post0); auto.
      + simpl. intros. fwd. eapply H. 2: auto. simpl. auto.
    - destruct post1; simpl in H1; try solve [destruct H1].
      destruct post2; simpl in H2; try solve [destruct H2].
      simpl. fwd. eauto.
  Qed.

  Lemma weaken: forall q t l m s post1,
      exec s q t m l post1 ->
      forall post2,
        implies post1 post2 ->
        exec s q t m l post2.
  Proof.
    induction 1; intros; simpl in *; fwd; try solve [econstructor; eauto].
    - eapply seq_cps_sorta; eauto. eapply weaken_sat; eauto.
    - eapply while_true_cps_sorta; eauto. eapply weaken_sat; eauto.
    - eapply stackalloc. 1: assumption.
      intros. specialize (H0 _ _ _ ltac:(eassumption) ltac:(eassumption)).
      fwd. exists prefix. split; [assumption|]. eapply weaken_sat; eauto.
      simpl. intros. fwd. destruct post0; try solve [destruct H0].
      exists post0. split; [reflexivity|]. simpl in H0. eauto 10.
    (* - eapply call. *)
    (*   4: eapply IHexec. *)
    (*   all: eauto. *)
    (*   intros. *)
    (*   edestruct H3 as (? & ? & ? & ? & ?); [eassumption|]. *)
    (*   eauto 10. *)
    - eapply interact; try eassumption.
      intros.
      edestruct H2 as (? & ? & ?); [eassumption|].
      eauto 10.
  Qed.

  (* Lemma intersect: forall s q t m l post1, *)
  (*     (forall t m l, post1 false t m l -> False) -> *)
  (*     exec s q t m l post1 -> *)
  (*     forall post2, *)
  (*       (forall t m l, post2 false t m l -> False) -> *)
  (*       exec s q t m l post2 -> *)
  (*       exec s q t m l (fun q' t' m' l' => post1 q' t' m' l' /\ post2 q' t' m' l'). *)
  (* Proof. *)
  (*   intros * Hpost1. *)
  (*   induction 1; *)
  (*     intros post2 Hpost2 ?; *)
  (*     match goal with *)
  (*     | H: exec _ _ _ _ _ _ |- _ => inversion H; *)
  (*                                 try solve [exfalso; eauto]; *)
  (*                                 subst; clear H *)
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
  (* Abort. (*this should be true, but looks like a few minutes of effort*) *)
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
  End WithParams.
End exec. Notation exec := exec.exec.

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
  
  Require Import Strings.String.
  Open Scope string_scope.
  Definition one : LogItem := ((map.empty, "1", nil), (map.empty, nil)).
  Import exec.
  Definition eventually_always_one :=
    exec.and_then (fun q' t' m' l' => True)
      (fun q' t' m' l' =>
       fun n =>
         exec.postcond (fun q'' t'' m'' l'' =>
                     t'' = (repeat one n ++ t')%list)).
  
  Definition eventually_always_one' (f : nat -> state) :=
    exists m, forall n,
    exists numsteps,
      (f numsteps).(t) = (repeat one n ++ (f m).(t))%list.

  Lemma eventually_always_one_right : forall f,
      interp_mids_and_post eventually_always_one f <-> eventually_always_one' f.
  Proof.
    intros. cbv [eventually_always_one eventually_always_one']. simpl. split; intros; fwd.
    - exists n. intros n0. specialize (Hp1 n0). fwd. exists n1.
      cbv [state_satisfies appl_to_state] in Hp1. assumption.
    - exists m0. split; [reflexivity|]. intros m. specialize (H m).
      fwd. exists numsteps. cbv [state_satisfies appl_to_state]. assumption.
  Qed.

  (*stackalloc 0 as x;
    while x-- { print 1 }
    while true { print 0 }*) Print expr.
  Definition countdown :=
    (cmd.while (expr.var "x")
                  (cmd.seq
                     (cmd.interact nil "0" nil)
                     (cmd.set "x" (expr.op bopname.sub (expr.var "x") (expr.literal 1))))).

  Context {locals_ok: map.ok locals}.

  Lemma countdown_terminates t m l xval :
    map.get l "x" = Some (word.of_Z xval) ->
    0 <= xval ->
    exec countdown true t m l (postcond (fun q' _ _ _ => q' = true)).
  Proof.
    intros. replace xval with (Z.of_nat (Z.to_nat xval)) in * by lia. clear H0.
    remember (Z.to_nat xval) as xval'.
    clear Heqxval' xval.
    remember xval' as upper_bound.
    rewrite Hequpper_bound in H.
    assert (xval' <= upper_bound)%nat  by lia. clear Hequpper_bound. revert xval' H0 H.
    revert t m l.
    induction upper_bound; intros.
    - eapply while_false.
      + simpl. rewrite H. reflexivity.
      + rewrite word.unsigned_of_Z. replace xval' with 0%nat by lia. reflexivity.
      + reflexivity.
    - assert (word.wrap (Z.of_nat xval') <> 0 \/ word.wrap (Z.of_nat xval') = 0) by lia.
      destruct H1.
      + eapply while_true_cps_sorta.
        -- simpl. apply H.
        -- rewrite word.unsigned_of_Z. assumption.
        -- eapply seq_cps_sorta.
           ++ eapply interact_cps.
              --- apply map.split_empty_r. reflexivity.
              --- reflexivity. 
              --- cbv [ext_spec]. eexists. intuition eauto.
                  instantiate (1 := fun q' _ _ l' => q' = true /\ map.get l' "x" = Some (word.of_Z (Z.of_nat xval'))). simpl. auto.
           ++ simpl. intros. fwd. eapply set.
              --- simpl. rewrite H2p1. reflexivity.
              --- instantiate (1 := fun q' _ _ l' => q' = true /\ map.get l' "x" = Some _). simpl. intuition auto. rewrite map.get_put_same. reflexivity.
        -- simpl. intros. fwd. eapply IHupper_bound.
           2: { rewrite H2p1. f_equal.
                instantiate (1 := Z.to_nat (word.unsigned _)). rewrite Z2Nat.id.
                2: { epose proof Properties.word.unsigned_range _ as H2. apply H2. }
                rewrite word.of_Z_unsigned. reflexivity. }
           enough (word.unsigned (word := word) (word.sub (word.of_Z (Z.of_nat xval')) (word.of_Z 1)) <= Z.of_nat upper_bound) by lia.
           pose proof Properties.word.decrement_nonzero_lt as H2.
           specialize (H2 (word.of_Z (Z.of_nat xval'))).
           rewrite word.unsigned_of_Z in H2. specialize (H2 H1).
           remember (word.unsigned _) as blah. clear Heqblah. enough (word.wrap (Z.of_nat xval') <= 1 + (Z.of_nat upper_bound)) by lia.
           clear H2 blah. cbv [word.wrap].
           pose proof Z.mod_le (Z.of_nat xval') (2 ^ width) as H2.
           specialize (H2 ltac:(lia)). eassert _ as blah. 2: specialize (H2 blah); lia.
           assert (2 ^ 0 <= 2 ^ width).
           { apply Z.pow_le_mono_r; try lia. destruct word_ok; clear - width_pos.
             lia. }
           lia.
      + eapply while_false; eauto. rewrite word.unsigned_of_Z. assumption.
  Qed.

  Definition one_printer :=
    (cmd.while (expr.literal 1) (cmd.interact nil "1" nil)).

  Lemma one_printer_prints_ones n t m l :
    exec one_printer true t m l
      (postcond (fun q' t' m' l' => q' = false /\ t' = repeat one n ++ t)%nat%list).
  Proof.
    revert t m l. induction n; intros t m l.
    - apply quit. simpl. auto.
    - eapply while_true_cps_sorta.
      + reflexivity.
      + apply one_not_zero.
      + eapply exec.interact_cps.
        -- apply map.split_empty_r. reflexivity.
        -- reflexivity.
        -- cbv [ext_spec]. eexists. intuition eauto.
           instantiate (1 := fun q' t' _ _ => q' = true /\ t' = one :: t).
           simpl. auto.
      + simpl. intros. fwd. eapply weaken. 1: apply IHn. simpl. intros.
        fwd. intuition auto.
        replace (repeat one n ++ one :: t)%list with (repeat one (S n) ++ t)%list.
        -- reflexivity.
        -- replace (S n) with (n + 1)%nat by lia. rewrite repeat_app.
           rewrite <- app_assoc. reflexivity.
  Qed.
          
  (* Lemma goes_forever e m l : *)
  (*   forall n, *)
  (*     exec e example true nil m l *)
  (*       (fun q' t' m' l' => q' = false /\ length t' = n). *)
  (* Proof. *)
  (*   intros. eapply exec.weaken. 1: apply goes_forever'. simpl. intros. fwd. eauto. *)
  (* Qed. *)

  Definition eventual_one_printer :=
    cmd.seq (cmd.stackalloc "x" 0 cmd.skip)
      (cmd.seq countdown one_printer).

  Lemma eventual_one_printer_eventually_always_one t m l : exec eventual_one_printer true t m l eventually_always_one.
  Proof.
    eapply seq_cps_sorta.
    { eapply stackalloc. 1: apply Zmod_0_l; lia. intros. eexists. split.
      { apply skip. instantiate (1 := fun q' t' m' l' => q' = true /\ t' = t /\ m' = mCombined /\ l' = map.put l "x" a). simpl. auto. }
      simpl. intros. fwd. eexists. split; [reflexivity|].
      eexists. eexists. split; [eassumption|]. split; [eassumption|].
      instantiate (1 := fun q' t' m' l' => exists a, q' = true /\ t' = t /\ m' = m /\ l' = map.put l "x" a).
      simpl. eauto. }
    simpl. intros. fwd. eapply seq_cps_sorta.
    { eapply countdown_terminates.
      - rewrite map.get_put_same. instantiate (1 := word.unsigned _). rewrite word.of_Z_unsigned. reflexivity.
      - pose proof Properties.word.unsigned_range a. lia. }
    simpl. intros. subst.
    (*Note: below gets stuck, as i guess it should*)
    (*eapply weaken. 1: apply one_printer_prints_ones. simpl.*)
    apply mid. 1: auto. intros n. eapply weaken.
    - apply (one_printer_prints_ones n).
    - simpl. intros. fwd. reflexivity.
  Qed.

  Lemma nested_quit t m l : exec (cmd.seq cmd.skip cmd.skip) true t m l (postcond (fun _ _ _ _ => True)).
  Proof.
    eapply seq_cps_for_real.
    apply exec.quit.
    Fail apply exec.skip. (*as it should be: cannot quit and then start executing again*)
    apply exec.quit.
    exact I.
  Qed.
End WithParams.
