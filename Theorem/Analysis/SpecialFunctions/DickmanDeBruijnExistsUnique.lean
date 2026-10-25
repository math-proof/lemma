/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/DickmanDeBruijnExistsUnique.lean -/

import Def.Analysis.SpecialFunctions.DickmanDeBruijn
import Lemma.Real.DickmanDeBruijn
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Def.Analysis.SpecialFunctions.DickmanDeBruijnExistsUnique
/-!
# Existence and uniqueness of the Dickman–de Bruijn function
-/


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
