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
import Lemma.Hyperreal.NotInfiniteDiv.of.InfinitesimalDivSquareSub.Infinite.Infinite
import Lemma.Int.Gt0Add.of.Lt_0.Lt_0
import Lemma.Int.Gt0Mul.of.Gt_0.Lt_0
import Lemma.Int.Gt0Mul.of.Lt_0.Gt_0
import Lemma.Int.Lt0Mul.of.Lt_0.Lt_0
import Lemma.Int.SquareSub
import Lemma.Nat.Add
import Lemma.Nat.Le.of.Lt
import Lemma.Nat.Lt0Mul.of.Gt_0.Gt_0
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
  (h : Infinitesimal ((a - b)² / (a² + b² + 1)))
  (h_0 : a > 0) :
-- imply
  b > 0 := by
-- proof
  have h_inf_ab := NotInfiniteDiv.of.InfinitesimalDivSquareSub.Infinite.Infinite h_a h_b h
  rw [SquareSub.comm] at h
  rw [Add.comm (a := a²)] at h
  have h_inf_ba := NotInfiniteDiv.of.InfinitesimalDivSquareSub.Infinite.Infinite h_b h_a h
  have h_a_ne_0 := Ne_0.of.Infinite h_a
  have h_b_ne_0 := Ne_0.of.Infinite h_b
  rw [DivSquareSub.eq.DivSubAddDivS.Ne_0.Ne_0 h_b_ne_0 h_a_ne_0] at h
  by_contra h_b_0
  simp at h_b_0
  have h_b_0 := Lt.of.Le.Ne  h_b_0 h_b_ne_0
  have h_div_ab_lt_0 := Gt0Div.of.Gt_0.Lt_0 h_0 h_b_0
  have h_div_ba_lt_0 := Gt0Div.of.Lt_0.Gt_0 h_b_0 h_0
  have h_mul_ba_lt_0 := Gt0Mul.of.Lt_0.Gt_0 h_b_0 h_0
  have h_inf_add_divs := NotInfiniteAdd.of.NotInfinite.NotInfinite h_inf_ab h_inf_ba
  have h_eps_sub : ¬(a / b + b / a - 2).Infinitesimal := by
    have h_le : a / b + b / a - 2 ≤ (-2 : ℝ) := by
      simp
      apply Le.of.Lt
      apply Gt0Add.of.Lt_0.Lt_0 h_div_ab_lt_0 h_div_ba_lt_0
    have h_inf_sub_add_divs : ¬(a / b + b / a - 2).Infinite := NotInfiniteSub.of.NotInfinite h_inf_add_divs (r := 2)
    have h_st_le := LeSt.of.Le.NotInfinite h_inf_sub_add_divs h_le
    apply NotInfinitesimal.of.NeSt_0
    linarith
  have h_inf_add : ¬(a / b + b / a + 1 / (b * a)).Infinite := by
    apply NotInfiniteAdd.of.NotInfinite.NotInfinite h_inf_add_divs
    apply NotInfiniteDiv.of.NotInfinite.NotInfinitesimal
    ·
      apply NotInfinitesimal.of.Infinite
      apply InfiniteMul.of.Infinite.Infinite h_b h_a
    ·
      apply NotInfinite
  have : NeZero (a / b + b / a + 1 / (b * a)) := ⟨
    by
      apply Ne.of.Lt
      apply Gt0Add.of.Lt_0.Lt_0
      ·
        apply Gt0Add.of.Lt_0.Lt_0 h_div_ab_lt_0 h_div_ba_lt_0
      ·
        have := Gt0Div.of.Lt_0.left (d := 1) h_mul_ba_lt_0
        simp at this
        simpa
  ⟩
  have := NotInfinitesimalDiv.of.NotInfinite.NotInfinitesimal h_eps_sub h_inf_add
  contradiction

-- created on 2025-12-22
