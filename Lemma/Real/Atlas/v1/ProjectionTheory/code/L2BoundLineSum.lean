import Mathlib
import sympy.Basic
import Def.v1.Atlas.ProjectionTheory.code.MainLemma2F
import Lemma.Real.Atlas.v1.ProjectionTheory.code.MainLemma2F
open Finset


namespace LineSumDecomposition

/--
[norm_sq_lineSumFn_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/L2BoundLineSum.lean)
-/
@[path]
lemma norm_sq_lineSumFn_le
  {p : ℕ}
  [Fact (Nat.Prime p)]
  {ℒ : Finset (Finset (ZMod p × ZMod p))}
-- given
  (hlines : ∀ L ∈ ℒ, L.card = p)
  (hinter : ∀ L₁ ∈ ℒ, ∀ L₂ ∈ ℒ, L₁ ≠ L₂ → (L₁ ∩ L₂).card ≤ 1) :
-- imply
  ∑ x : ZMod p × ZMod p, (lineSumFn ℒ x) ^ 2 ≤ (ℒ.card : ℝ) ^ 2 + (ℒ.card : ℝ) * (p : ℝ) := by
-- proof
  have hdecomp : ∀ x : ZMod p × ZMod p,
    (lineSumFn ℒ x) ^ 2 =
    (lineSumConst ℒ) ^ 2 + 2 * lineSumConst ℒ * lineSumHighFreq ℒ x +
    (lineSumHighFreq ℒ x) ^ 2 := by
    intro x
    have h := decomposition ℒ x
    rw [h]; ring
  simp_rw [hdecomp, Finset.sum_add_distrib]
  have hcross : ∑ x : ZMod p × ZMod p,
    2 * lineSumConst ℒ * lineSumHighFreq ℒ x = 0 := by
    rw [show (fun x => 2 * lineSumConst ℒ * lineSumHighFreq ℒ x) =
      (fun x => 2 * (lineSumConst ℒ * lineSumHighFreq ℒ x)) from by ext x; ring]
    rw [← Finset.mul_sum]
    rw [orthogonal_const_highFreq ℒ hlines]
    ring
  rw [hcross, add_zero]
  have h_const := norm_sq_const_eq ℒ
  have h_high := norm_sq_highFreq_le ℒ hlines hinter
  linarith

end LineSumDecomposition


-- created on 2026-10-23
