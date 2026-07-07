import Lemma.Hyperreal.GtSt_0.of.Gt_0.NotInfinite.NotInfinitesimal
import Lemma.Hyperreal.Gt_0.of.GtSt_0
import Lemma.Hyperreal.NotInfiniteMul.of.NotInfinite.NotInfinite
import Lemma.Hyperreal.Infinitesimal.of.InfinitesimalMul.NotInfinitesimal
import Lemma.Hyperreal.StInv.eq.InvSt
import Lemma.Rat.Lt0Div.is.Lt0Mul
open Hyperreal Rat


@[main]
private lemma main
  {a b : ℝ*}
-- given
  (h_a : ¬a → 0)
  (h_b : ¬b → 0)
  (h_a_inf : ¬a → ∞)
  (h_b_inf : ¬b → ∞)
  (h : stdPart (a / b) > 0) :
-- imply
  stdPart (a * b)⁻¹ > 0 := by
-- proof
  rw [StInv.eq.InvSt]
  simp
  apply GtSt_0.of.Gt_0.NotInfinite.NotInfinitesimal
  ·
    apply NotInfinitesimalMul.of.NotInfinitesimal.NotInfinitesimal h_a h_b
  ·
    apply NotInfiniteMul.of.NotInfinite.NotInfinite h_a_inf h_b_inf
  ·
    apply Lt0Mul.of.Lt0Div
    apply Gt_0.of.GtSt_0 h


-- created on 2025-12-18
