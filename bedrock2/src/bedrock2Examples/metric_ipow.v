Require Import Coq.ZArith.ZArith coqutil.Z.div_mod_to_equations.
Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2.MetricLogging.
Require Import bedrock2.MetricCosts.
Import Syntax BinInt String List.ListNotations ZArith.
Require Import coqutil.Z.Lia.
Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.

Definition ipow := func! (x, e) ~> ret {
  ret = $1;
  while (e) {
    if (e & $1) { ret = ret * x };
    e = e >> $1;
    x = x * x
  }
}.

From bedrock2 Require Import BasicC64Semantics MetricWeakestPrecondition MetricProgramLogic.
From bedrock2 Require Import MetricLoops.
From coqutil Require Import Word.Properties Word.Interface Tactics.letexists.
Import Interface.word.

Definition initCost := {| instructions := 12; stores := 2; loads := 13; jumps := 0 |}.
Definition iterCost := {| instructions := 76; stores := 16; loads := 98; jumps := 2 |}.
Definition endCost :=  {| instructions := 6; stores := 1; loads := 9; jumps := 1 |}.

Definition msb z := match z with
                    | Zpos _ => Z.log2 z + 1
                    | _ => 0
                    end.

#[export] Instance spec_of_ipow : spec_of "ipow" :=
  fnspec! "ipow" x e ~> v,
  { requires t m mc := True;
    ensures t' m' mc' := unsigned v = unsigned x ^ unsigned e mod 2^64 /\
      (mc' - mc <= initCost + (msb (word.unsigned e)) * iterCost + endCost)%metricsH
  }.

Module Z.
  Lemma pow_mod x n m (Hnz: m <> 0) : (x mod m)^n mod m = x^n mod m.
  Proof.
    revert n.
    eapply Z.order_induction_0; intros.
    { intros ???; subst; split; auto. }
    { rewrite 2Z.pow_0_r; trivial. }
    { rewrite 2Z.pow_succ_r by trivial.
      rewrite <-Z.mul_mod_idemp_r by trivial.
      multimatch goal with H: _ |- _ => rewrite H end;
      rewrite Z.mul_mod_idemp_l, Z.mul_mod_idemp_r; solve[trivial]. }
    { rewrite 2Z.pow_neg_r; trivial. }
  Qed.

  Lemma mod2_nonzero x : x mod 2 <> 0 -> x mod 2 = 1.
  Proof. Z.div_mod_to_equations. blia. Qed.

  Lemma land_1_r x : Z.land x 1 = x mod 2.
  Proof.
    change 1 with (Z.ones 1) in *.
    rewrite Z.land_ones in * by discriminate.
    exact eq_refl.
  Qed.
End Z.

Require Import bedrock2.AbsintWordToZ coqutil.Z.Lia.

Ltac t :=
  repeat match goal with x := _ |- _ => subst x end;
  repeat match goal with |- context [word.unsigned ?e] => progress (idtac; let H := rbounded (word.unsigned e) in idtac) end;
  repeat match goal with G: context [word.unsigned ?e] |- _ => progress (idtac; let H := rbounded (word.unsigned e) in idtac) end;
  repeat match goal with |- context [word.unsigned ?e] => progress (idtac; let H := unsigned.zify_expr e in try rewrite H) end;
  repeat match goal with G: context [word.unsigned ?e] |- _ => progress (idtac; let H := unsigned.zify_expr e in try rewrite H in G) end;
  repeat match goal with H: absint_eq ?x ?x |- _ => clear H end;
  cbv [absint_eq] in *.

Lemma msb_shift z : 0 < z -> msb (z / 2) = msb z - 1.
Proof.
  intro.
  case (z / 2) eqn:Hdiv.
  - enough (H1 : z = 1) by (rewrite H1; easy).
    enough (z = z mod 2) by (Z.div_mod_to_equations; blia).
    rewrite (Z.div_mod z 2) by blia.
    rewrite Hdiv.
    cbn.
    rewrite Zmod_mod.
    reflexivity.
  - rewrite <- Z.div2_div in Hdiv.
    rewrite (Zdiv2_odd_eqn z).
    rewrite Hdiv.
    rewrite <- Pos2Z.inj_mul.
    case (Z.odd z);
    [rewrite <- Pos2Z.inj_add | rewrite Z.add_0_r];
    unfold msb;
    rewrite Z.add_simpl_r;
    [rewrite Pos2Z.inj_add |]; rewrite Pos2Z.inj_mul;
    [rewrite Z.log2_succ_double | rewrite Z.log2_double];
    blia.
  - pose proof (Zlt_neg_0 p) as Hneg.
    rewrite <- Hdiv in Hneg.
    Z.div_mod_to_equations.
    blia.
Qed.

Ltac s := unfold initCost, iterCost, endCost in *;
          cost_unfold;
          cbn in *;
          solve_MetricLog.

Lemma ipow_ok : program_logic_goal_for_function! ipow.
Proof.
  repeat straightline.
  match goal with H : True |- _ => clear H end.

  refine ((MetricLoops.tailrec
    (* types of ghost variables*) HList.polymorphic_list.nil
    (* program variables *) (["e";"ret";"x"] : list String.string))
    (fun v t m e ret x mc => PrimitivePair.pair.mk (v = word.unsigned e) (* precondition *)
    (fun   T M E RET X MC => T = t /\ M = m /\ (* postcondition *)
        word.unsigned RET = word.unsigned ret * word.unsigned x ^ word.unsigned e mod 2^64 /\
        (MC - mc <= msb (word.unsigned e) * iterCost + endCost)%metricsH))
    (fun n m => 0 <= n < m) (* well_founded relation *)
    _ _ _ _ _);
    (* TODO wrap this into a tactic with the previous refine *)
    cbn [HList.hlist.foralls HList.tuple.foralls
         HList.hlist.existss HList.tuple.existss
         HList.hlist.apply  HList.tuple.apply
         HList.hlist
         List.repeat Datatypes.length
         HList.polymorphic_list.repeat HList.polymorphic_list.length
         PrimitivePair.pair._1 PrimitivePair.pair._2] in *.

  { repeat straightline. }
  { exact (Z.lt_wf _). }
  { repeat straightline. } (* init precondition *)
  { (* loop test *)
    repeat straightline; try show_program.
    { (* loop body *)
      eexists; eexists; split; [repeat straightline|]. (* if condition evaluation *)
      split. (* if cases, path-blasting *)
      {
        repeat (straightline || (split; trivial; [])). 2: split. all:t.
        { (* measure decreases *)
          set (word.unsigned x0) in *. (* WHY does blia need this? *)
          Z.div_mod_to_equations. blia. }
        { (* invariant preserved *)
          rewrite H3; clear H3. rename H0 into Hbit.
          change (1+1) with 2 in *.
          eapply Z.mod2_nonzero in Hbit.
          epose proof (Z.div_mod _ 2 ltac:(discriminate)) as Heq; rewrite Hbit in Heq.
          rewrite Heq at 2; clear Hbit Heq.
          (* rewriting with equivalence modulo ... *)
          rewrite !word.unsigned_mul.
          unfold word.wrap.
          rewrite ?Z.mul_mod_idemp_l by discriminate.
          rewrite <-(Z.mul_mod_idemp_r _ (_^_)), Z.pow_mod by discriminate.
          rewrite ?Z.pow_add_r by (pose proof word.unsigned_range x0; Z.div_mod_to_equations; blia).
          rewrite ?Z.pow_twice_r, ?Z.pow_1_r, ?Z.pow_mul_l.
          rewrite Z.mul_mod_idemp_r by discriminate.
          f_equal; ring. }
        { (* metrics correct *)
          rewrite msb_shift in H4 by blia.
          rewrite MetricArith.mul_sub_distr_r in H4.
          rewrite <- MetricArith.add_sub_swap in H4.
          rewrite <- MetricArith.le_add_le_sub_r in H4.
          eapply MetricArith.le_trans with (2 := H4).
          s.
        }
      }
      {
        repeat (straightline || (split; trivial; [])). 2: split. all: t.
        { (* measure decreases *)
          set (word.unsigned x0) in *. (* WHY does blia need this? *)
          Z.div_mod_to_equations; blia. }
        { (* invariant preserved *)
          rewrite H3; clear H3. rename H0 into Hbit.
          change (1+1) with 2 in *.
          epose proof (Z.div_mod _ 2 ltac:(discriminate)) as Heq; rewrite Hbit in Heq.
          rewrite Heq at 2; clear Hbit Heq.
          (* rewriting with equivalence modulo ... *)
          rewrite !word.unsigned_mul, ?Z.mul_mod_idemp_l by discriminate.
          cbv [word.wrap].
          rewrite <-(Z.mul_mod_idemp_r _ (_^_)), Z.pow_mod by discriminate.
          rewrite ?Z.add_0_r, Z.pow_twice_r, ?Z.pow_1_r, ?Z.pow_mul_l.
          rewrite Z.mul_mod_idemp_r by discriminate.
          f_equal; ring. }
        { (* metrics correct *)
          rewrite msb_shift in H4 by blia.
          s.
        }
      }
    }
    { (* postcondition *)
      rewrite H, Z.pow_0_r, Z.mul_1_r, word.wrap_unsigned.
      split; [reflexivity|].
      unfold msb; subst brmc.
      s.
    }
  }

  repeat straightline.

  repeat (split || letexists || t || trivial).
  { setoid_rewrite H1; setoid_rewrite Z.mul_1_l; trivial. }
  all: s.
Qed.
