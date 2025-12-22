import Lemma.Hyperreal.NotInfiniteInv.of.Infinite
import Lemma.Int.GtAbs_0.of.Lt_0
import Lemma.Int.GtAbs_0.of.Gt_0
import Lemma.Nat.Lt0Add.of.Gt_0.Gt_0
import Lemma.Rat.DivAbsSub.eq.DivAbsSubDiv.Ne_0.Ne_0
import Lemma.Hyperreal.EqSt_0.of.Infinitesimal
import Lemma.Hyperreal.Infinite.is.InfiniteAdd.of.NotInfinite
import Lemma.Hyperreal.Infinite.is.InfiniteSub
import Lemma.Hyperreal.Infinite.of.InfiniteDiv.NotInfinitesimal
import Lemma.Hyperreal.Infinite.of.InfinitesimalDiv.NotInfinitesimal
import Lemma.Hyperreal.InfiniteMul.of.Infinite.Infinite
import Lemma.Hyperreal.LeSt.of.Le.NotInfinite
import Lemma.Hyperreal.Ne_0.of.Infinite
import Lemma.Hyperreal.NotInfinite
import Lemma.Hyperreal.NotInfinite.of.Infinitesimal
import Lemma.Hyperreal.NotInfiniteDiv.of.InfinitesimalDivAbsSub.Infinite.Infinite
import Lemma.Int.AbsSub
import Lemma.Int.Gt0Add.of.Lt_0.Lt_0
import Lemma.Int.Gt0Mul.of.Lt_0.Gt_0
import Lemma.Nat.Add
import Lemma.Nat.Le.of.Lt
import Lemma.Nat.Ne.of.Lt
import Lemma.Rat.DivSquareSub.eq.DivSubAddDivS.Ne_0.Ne_0
import Lemma.Rat.Gt0Div.of.Gt_0.Lt_0
import Lemma.Rat.Gt0Div.of.Lt_0
import Lemma.Rat.Gt0Div.of.Lt_0.Gt_0
open Hyperreal Int Nat Rat


@[main]
private lemma main
  {a b : ℝ*}
-- given
  (h_a : a.Infinite)
  (h_b : b.Infinite)
  (h : Infinitesimal (|a - b| / (|a| + |b| + 1)))
  (h_0 : a > 0) :
-- imply
  b > 0 := by
-- proof
  have h_inf_ab := NotInfiniteDiv.of.InfinitesimalDivAbsSub.Infinite.Infinite h_a h_b h
  rw [AbsSub.comm] at h
  rw [Add.comm (a := |a|)] at h
  have h_inf_ba := NotInfiniteDiv.of.InfinitesimalDivAbsSub.Infinite.Infinite h_b h_a h
  have h_a_ne_0 := Ne_0.of.Infinite h_a
  have h_b_ne_0 := Ne_0.of.Infinite h_b
  rw [Rat.DivAbsSub.eq.DivAbsSubDiv.Ne_0.Ne_0 h_a_ne_0] at h
  by_contra h_b_0
  simp at h_b_0
  have h_b_0 := Lt.of.Le.Ne h_b_0 h_b_ne_0
  have h_div_ab_lt_0 := Gt0Div.of.Gt_0.Lt_0 h_0 h_b_0
  have h_div_ba_lt_0 := Gt0Div.of.Lt_0.Gt_0 h_b_0 h_0
  have h_mul_ba_lt_0 := Gt0Mul.of.Lt_0.Gt_0 h_b_0 h_0
  have h_inf_add_divs : ¬(b / a - 1).Infinite := NotInfiniteSub.of.NotInfinite h_inf_ba (r := 1)
  have h_eps_sub : ¬|b / a - 1|.Infinitesimal := by
    apply NotInfinitesimalAbs.of.NotInfinitesimal
    have h_le : b / a - 1 ≤ (-1 : ℝ) := by
      simp
      apply Le.of.Lt h_div_ba_lt_0
    have h_st_le := LeSt.of.Le.NotInfinite h_inf_add_divs h_le
    apply NotInfinitesimal.of.NeSt_0
    linarith
  have h_inf_add : ¬(|b / a| + |a|⁻¹ + 1).Infinite := by
    apply NotInfiniteAdd.of.NotInfinite.NotInfinite
    .
      apply NotInfiniteAdd.of.NotInfinite.NotInfinite
      .
        apply NotInfiniteAbs.of.NotInfinite h_inf_ba
      .
        apply NotInfiniteInv.of.Infinite
        apply InfiniteAbs.of.Infinite h_a
    .
      apply NotInfinite
  have : NeZero (|b / a| + |a|⁻¹ + 1) := ⟨
    by
      apply Ne.of.Gt
      apply Lt0Add.of.Gt_0.Gt_0
      .
        apply Lt0Add.of.Gt_0.Gt_0
        .
          apply GtAbs_0.of.Lt_0 h_div_ba_lt_0
        .
          apply GtInv_0.of.Gt_0
          apply GtAbs_0.of.Gt_0 h_0
      .
        simp
  ⟩
  have := NotInfinitesimalDiv.of.NotInfinite.NotInfinitesimal h_eps_sub h_inf_add
  contradiction


-- created on 2025-12-22
