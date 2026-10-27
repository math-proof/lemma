import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.PiL2
import Initialize.Tactic.Attr.Basic
open InnerProductSpace


@[path]
private lemma main
  {n : ℕ} {b x : EuclideanSpace ℝ (Fin n)} {c : ℝ} :
-- imply
  gradient (fun y : EuclideanSpace ℝ (Fin n) => c + ⟪b, y⟫_ℝ) x = b := by
-- proof
  have hlin : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin n) => ⟪b, y⟫_ℝ) (innerSL ℝ b) x :=
    (innerSL ℝ b).hasFDerivAt
  apply HasGradientAt.gradient
  rw [hasGradientAt_iff_hasFDerivAt]
  convert hlin.const_add c using 1
  ext y
  simp [toDual_apply_apply, innerSL_apply_apply]


-- created on 2021-12-25
-- updated on 2026-10-26
