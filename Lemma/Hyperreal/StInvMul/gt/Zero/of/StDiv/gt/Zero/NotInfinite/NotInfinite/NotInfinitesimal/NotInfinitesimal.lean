import Lemma.Hyperreal.GtSt_0.of.Gt_0.NotInfinite.NotInfinitesimal
import Lemma.Hyperreal.Gt_0.of.GtSt_0
import Lemma.Hyperreal.NotInfiniteMul.of.NotInfinite.NotInfinite
import Lemma.Hyperreal.Infinitesimal.of.InfinitesimalMul.NotInfinitesimal
import Lemma.Hyperreal.StInv.eq.InvSt
import Lemma.Rat.Div.gt.Zero.is.Mul.gt.Zero
open Hyperreal Rat


@[main]
private lemma main
  {a b : ℝ*}
-- given
  (h_a : ¬Infinitesimal a)
  (h_b : ¬Infinitesimal b)
  (h_a_inf : ¬Infinite a)
  (h_b_inf : ¬Infinite b)
  (h : st (a / b) > 0) :
-- imply
  st (a * b)⁻¹ > 0 := by
-- proof
  rw [StInv.eq.InvSt]
  simp
  apply GtSt_0.of.Gt_0.NotInfinite.NotInfinitesimal
  ·
    apply NotInfinitesimalMul.of.NotInfinitesimal.NotInfinitesimal h_a h_b
  ·
    apply NotInfiniteMul.of.NotInfinite.NotInfinite h_a_inf h_b_inf
  ·
    apply Mul.gt.Zero.of.Div.gt.Zero
    apply Gt_0.of.GtSt_0 h


-- created on 2025-12-18
