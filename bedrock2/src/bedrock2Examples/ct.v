Require Import Coq.ZArith.ZArith coqutil.Z.div_mod_to_equations.
Require Import bedrock2.NotationsCustomEntry.
Import Syntax BinInt String List.ListNotations ZArith.
Require Import coqutil.Z.Lia.
Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.

Definition div3329_vartime := func! (x) ~> ret {
  ret = $(expr.op bopname.divu "x" 3329)
}.

Definition div3329 := func! (x) ~> ret {
  ret = (x * $989558401) >> $32;
  ret = (ret + (x - ret >> $1)) >> $11
}.

From coqutil Require Import Word.Properties Word.Interface Tactics.letexists.
Import Interface.word Coq.Lists.List List.ListNotations.
From bedrock2 Require Import Semantics BasicC32Semantics WeakestPrecondition ProgramLogic.
Import ProgramLogic.Coercions.

#[global] Instance ctspec_of_div3329 : spec_of "div3329" :=
  fun functions => forall k, exists k_, forall t m x,
      WeakestPrecondition.call functions "div3329" k t m [x]
        (fun k' t' m' rets => exists ret, rets = [ret]
        /\ t' = t /\ m' = m /\ k' = k_
        (*x < 2^32 -> ret = x / 3329 :> Z*) ).

Lemma div3329_ct : program_logic_goal_for_function! div3329.
Proof.
  repeat (straightline || eexists).
  { (* no leakag -- 3 minutes *) cbv [k' k'0]. cbn. exact eq_refl. }
Qed.

#[global] Instance vtspec_of_div3329 : spec_of "div3329_vartime" :=
  fun functions => forall k, forall t m x,
      WeakestPrecondition.call functions "div3329_vartime" k t m [x]
        (fun k' t' m' rets => exists ret, rets = [ret]
        /\ t' = t /\ m' = m /\ k' = [leak_word (word.of_Z 3329); leak_word x]++k
        (*x < 2^32 -> ret = x / 3329 :> Z*) ).

Lemma div3329_vt : program_logic_goal_for_function! div3329_vartime.
Proof.
  repeat (straightline || eexists).
Qed.

(* Mon Jul  1 14:14:15 EDT 2024 *)

Import Byte.
Definition getchar_event c : io_event :=
  ((Interface.map.empty, "getchar", []), (Interface.map.empty, [word.of_Z (byte.unsigned c)])).
#[global] Instance ctspec_of_getchar : spec_of "getchar" :=
  fun functions => forall k, exists k_, forall t m,
      WeakestPrecondition.call functions "getchar" k t m []
        (fun k' t' m' rets => exists c, rets = [word.of_Z (byte.unsigned c)] /\ k' = k_ /\ m' = m /\
        t' = cons (getchar_event c) t ).

Definition getline := func! (dst, n) ~> n {
  i = $0;
  c = $0;
  while (i < n) {
    unpack! c = getchar();
    if (c == $0x0a) { n = i }
    else { store1(dst + i, c); i = i + $1 }
  }
}.

Local Notation "xs $@ a" := (Array.array Separation.ptsto (word.of_Z 1) a xs) (at level 10, format "xs $@ a").
Local Infix "*" := Separation.sep.
Local Infix "*" := Separation.sep : type_scope.

Definition getline_io bs := getchar_event Byte.x0a :: map getchar_event (rev bs).

#[global] Instance ctspec_of_getline : spec_of "getline" :=
  fun functions => exists f, forall k (dst n : word) d t m R,
  (d$@dst * R) m -> length d = n :> Z ->
      WeakestPrecondition.call functions "getline" k t m [dst; n]
        (fun k' t' m' rets => exists bs es l, rets = [l] /\ k' = f k l ++ k /\
        (bs$@dst * es$@(word.add dst l) * R) m' /\
        length bs = l :> Z /\
        length bs + length es = n :> Z /\
        (* TODO: handle case where buffer is full and final newline is not read. possibly just as an error. *)
        t' = getline_io bs ++ t).

(* Mon Jul  1 14:24:28 EDT 2024 *)

Require Coq.Program.Wf.
Import Separation SeparationLogic.

Lemma getline_ct : program_logic_goal_for_function! getline.
Proof.
  repeat straightline.

  refine ((Loops.tailrec_earlyout
    (HList.polymorphic_list.cons (list byte)
    (HList.polymorphic_list.cons (_ -> Prop)
    HList.polymorphic_list.nil))
    ["dst";"n";"i";"c"])
    (fun (v:nat) es R k t m  dst_ n_ i c => PrimitivePair.pair.mk (
      n_ = n /\ dst_ = dst /\ v = i :> Z /\
      (* TODO: i <= n *)
      (es$@(word.add dst i) * R) m /\ length es = word.sub n i :> Z
    )
    (fun                K T M DST N I C => DST = dst /\
      exists bs ES, (bs$@(word.add dst i) * ES$@(word.add dst I) * R) M /\ I = N /\
      length bs = word.sub I i :> Z /\
      length ES = word.sub n I :> Z /\
      (* TODO: N <= n *)
      T = getline_io bs ++ t
    ))
    (fun i j : nat => j < i <= n)%Z
    _ _ _ _ _ _ _);
    cbn [HList.hlist.foralls HList.tuple.foralls
         HList.hlist.existss HList.tuple.existss
         HList.hlist.apply  HList.tuple.apply
         HList.hlist
         List.repeat Datatypes.length
         HList.polymorphic_list.repeat HList.polymorphic_list.length
         PrimitivePair.pair._1 PrimitivePair.pair._2] in *;
    repeat straightline.
    { eapply (Wf.measure_wf (Z.gt_wf _) Z.of_nat). }
    { split.
      { instantiate (1:=O). subst v. rewrite word.unsigned_of_Z. exact eq_refl. }
      { subst v; rewrite word.add_0_r; split; [ecancel_assumption|]. rewrite word.sub_0_r; auto. } }

    { let e := open_constr:(_) in specialize (H e); destruct H.
      eapply WeakestPreconditionProperties.Proper_call; repeat intro; cycle 1.
      { refine (H _ _). }
      repeat straightline.
      eexists _, _; repeat straightline.
      split; repeat straightline.
      split; repeat straightline.
      { left; repeat straightline.
        { subst br'. rewrite unsigned_ltu, Z.ltb_irrefl; trivial. }
        eexists _, _; repeat straightline.
        eapply word.if_nonzero, word.eqb_true in H3.
        instantiate (1:=nil); cbn [Array.array]; split.
        { ecancel_assumption. }
        { cbv [getline_io map rev List.app].
          split; trivial.
          split.
          { admit. }
          split; trivial.
          eapply f_equal2; f_equal; trivial.
          change 10 with (byte.unsigned Byte.x0a) in H3.
          pose proof byte.unsigned_range x2.
          pose proof byte.unsigned_range Byte.x0a.
          eapply word.of_Z_inj_small, byte.unsigned_inj in H3; trivial; blia. } }

      (* store *)
      destruct x as [|x_0 x].
      { cbn [length] in *.
        assert (n = x3) as -> by (revert H3; admit).
        subst br. rewrite unsigned_ltu, Z.ltb_irrefl in H2; case H2; exact eq_refl. }
      cbn [Array.array] in *.
      repeat straightline.
      right; repeat straightline.
      eexists _, _, _; repeat straightline.
      { instantiate (1:=x).
        subst v3.
        rewrite word.add_assoc.
        split.
        { instantiate (1:=S v1). admit. }
        split; [ecancel_assumption|].
        cbn [length] in *.
        (* Require Import ZnWords. ZnWords. *)
        admit. }
      { split.
        { admit. }
        repeat straightline.
        (* subroutine return *)
        subst a.
        subst v3.

        rename x10 into bs.
        rename x11 into es.
        rename x6 into I.
        rename x3 into _i.
        rewrite word.add_assoc in H9.

        eexists (byte.of_Z v2::bs), (es).
        cbn ["$@" "++"].
        split. { ecancel_assumption. }
        split; trivial.
        split.
        { cbn [length]. rewrite Nat2Z.inj_succ, H11. admit. }
        split; trivial.
        subst T a0. cbn. rewrite map_app; cbn.
        repeat rewrite <-?app_comm_cons, <-?app_assoc; f_equal.
        f_equal.
        f_equal.
        f_equal.
        subst v2.
        rewrite word.unsigned_of_Z_nowrap, byte.of_Z_unsigned by admit; trivial. } }

    { (* buffer full *)
      replace x3 with n in * by admit.
      exists x, nil; cbn [Array.array].
      split. { ecancel_assumption. }
      split. { trivial. }
      split. { trivial. }
      assert (length x = O) by admit.
      split. { admit. }
      destruct x; cbn [length] in *; try blia; cbn.

      admit. (* <==== TODO: this one is false: if the buffer is full then the I/O trace does not end with newline *)
    }

    split. { admit. (* leakage *) }
    subst v.
    rewrite word.add_0_r in *.
    split.
    { ecancel_assumption. }
    split.
    { rewrite H5. rewrite word.sub_0_r. trivial. }
    split.
    { rewrite H5, H6, word.sub_0_r. admit. }
    subst t0.
    trivial.

(* Tue Jul  2 14:26:41 EDT 2024 *)
Admitted.

Require Import bedrock2Examples.memequal.

(*TODO: take username via IO, not as argument.*)
Definition password_checker := func! (username, password_array) ~> ret {
                                   stackalloc 8 as x; (*password is 8 characters*)
                                   unpack! attempt = getline(x, $8);
                                   unpack! ret = memequal(x, password_array + username * $8, $8)
                                 }.

#[global] Instance ctspec_of_password_checker : spec_of "password_checker" :=
  fun functions => forall pick_sp k (username password_array : word), exists k_, forall n R t m passwords,
      length passwords = Nat.mul n 8 ->
      word.unsigned username < n ->
      (passwords$@password_array * R) m ->
      WeakestPrecondition.call functions "password_checker" k t m [username; password_array]
        (fun k' t' m' rets =>
           exists k'', k' = k'' ++ k /\
                         (predicts pick_sp (rev k'') -> k' = k_)).

Fail Lemma password_checker_ct : program_logic_goal_for_function! password_checker. (*Why*)
Global Instance spec_of_memequal : spec_of "memequal" := spec_of_memequal.

Lemma password_checker_ct : program_logic_goal_for_function! password_checker.
Proof.
  repeat straightline.
  eapply WeakestPreconditionProperties.Proper_call; repeat intro; cycle 1.
  { apply Array.anybytes_to_array_1 in H4. destruct H4 as [bs [Hbs Hlenbs]].
    eapply H. 2: eassumption. ecancel_assumption. }
  repeat straightline.
  eapply WeakestPreconditionProperties.Proper_call; repeat intro; cycle 1.
  { eapply H0. split. { ecancel_assumption. } split.
    { admit. } admit. }
  repeat straightline. eexists. eexists. split; [admit|split; [admit|]].
  repeat straightline. eexists. subst. split; [trace_alignment|].
  intros Hpred. repeat (rewrite rev_app_distr in Hpred || cbn [rev] in Hpred).
  repeat rewrite <- app_assoc in Hpred. cbn [List.app] in Hpred. inversion Hpred; clear Hpred; subst.
  specialize (H14 I). instantiate (1 := match (pick_sp nil) with | consume_word _ => _ |_ => _ end). (*^we have to do this because pick_sp does not return a word. probably it should return a word.*)
  rewrite H14. subst.
  (*TODO: cannot prove this because we leak the length of the password that is input.
    Should update spec to say something about IO trace.*)
Abort.

Definition maskloop := func! (a) {
  i = $0;
  while (i < $2) {
    mask = $0-((load1(a+i)>>i)&$1);
    store1(a+i, mask & $123);
    i = i + $1
  }
}.

Require Import coqutil.Map.Interface bedrock2.Map.Separation bedrock2.Map.SeparationLogic.

#[global] Instance ctspec_of_maskloop : spec_of "maskloop" :=
  fun functions => forall k a, exists k_, forall a0 a1 R t m,
      m =* ptsto a a0 * ptsto (word.add a (word.of_Z 1)) a1 * R ->
      WeakestPrecondition.call functions "maskloop" k t m [a]
        (fun k' t' m' rets => rets = [] /\ k' = k_).

Lemma maskloop_ct : program_logic_goal_for_function! maskloop.
Proof.
  repeat straightline.
  eexists nat, lt, (fun i k _ (m : mem) (l : locals) =>
    map.get l "a" = Some a /\
    map.get l "i" = Some (word.of_Z (Z.of_nat i)) /\ (
    i = 0%nat /\ m =* ptsto a a0 * ptsto (word.add a (word.of_Z 1)) a1 * R \/
    i = 1%nat /\ False \/
    i = 2%nat /\ False)).
  Tactics.ssplit; auto using lt_wf.
  { exists 0%nat; Tactics.ssplit.
    { subst l0 l; rewrite map.get_put_diff, map.get_put_same; congruence. }
    { subst l0 l v. rewrite map.get_put_same; trivial. }
    left; Tactics.ssplit; trivial; ecancel_assumption. }
  intuition subst.
Abort.
