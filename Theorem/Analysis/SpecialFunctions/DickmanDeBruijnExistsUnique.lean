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
public import Def.Analysis.SpecialFunctions.DickmanDeBruijnExistsUnique

/-!
# Existence and uniqueness of the Dickman–de Bruijn function
-/

public section


section

namespace Real

lemma dickApprox_eq_one_of_le_one : ∀ (n : ℕ) (x : ℝ), x ≤ 1 → dickApprox n x = 1
  | 0, x, _ => rfl
  | n + 1, x, hx => by
    simp only [dickApprox, dickStep]
    have hmax : max x 1 = 1 := max_eq_right hx
    rw [hmax]
    simp

end Real
end
