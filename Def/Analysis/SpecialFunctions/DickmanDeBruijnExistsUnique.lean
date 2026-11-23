/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/DickmanDeBruijnExistsUnique.lean -/

module

public import Def.Analysis.SpecialFunctions.DickmanDeBruijn
public import Theorem.Real.DickmanDeBruijn
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Existence and uniqueness of the Dickman–de Bruijn function
-/


section

namespace Real

/-- Method-of-steps approximants for the Dickman–de Bruijn function. -/
noncomputable def dickStep (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  1 - ∫ t in (1 : ℝ)..(max x 1), f (t - 1) / max t 1

noncomputable def dickApprox : ℕ → (ℝ → ℝ)
  | 0 => fun _ => 1
  | n + 1 => dickStep (dickApprox n)

end Real
end
