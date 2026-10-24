/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/DickmanDeBruijnExistsUnique.lean -/

import sympy.atlas.Analysis.SpecialFunctions.DickmanDeBruijn
import Lemma.Real.DickmanDeBruijn
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Existence and uniqueness of the Dickman–de Bruijn function
-/

section
namespace Real

/-- Method-of-steps approximants for the Dickman–de Bruijn function. -/
private noncomputable def dickStep (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  1 - ∫ t in (1 : ℝ)..(max x 1), f (t - 1) / max t 1

private noncomputable def dickApprox : ℕ → (ℝ → ℝ)
  | 0 => fun _ => 1
  | n + 1 => dickStep (dickApprox n)

private lemma dickApprox_eq_one_of_le_one : ∀ (n : ℕ) (x : ℝ), x ≤ 1 → dickApprox n x = 1
  | 0, x, _ => rfl
  | n + 1, x, hx => by
    simp only [dickApprox, dickStep]
    have hmax : max x 1 = 1 := max_eq_right hx
    rw [hmax]
    simp

private noncomputable def dickRho (x : ℝ) : ℝ :=
  if x < 0 then 0 else dickApprox ⌈x⌉₊ x
end Real
end
