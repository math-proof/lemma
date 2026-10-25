import Mathlib
import sympy.Basic
import Def.v1.Atlas.BooleanFunctions.code.Influence
open BooleanFourier


namespace BooleanFourier

/--
[totalInfluence_eq_expected_pivotal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/Influence.lean)
-/
@[path]
lemma totalInfluence_eq_expected_pivotal
  {n : ℕ}
  {f : (Fin n → Bool) → Bool} :
-- imply
  totalInfluence f = (1 / (2 : ℝ) ^ n) * ∑ x : Fin n → Bool, (numPivotal f x : ℝ) := by
-- proof
  unfold totalInfluence influence numPivotal
  rw [← Finset.sum_div, one_div, inv_mul_eq_div]
  congr 1
  simp only [Finset.card_filter]
  push_cast
  rw [Finset.sum_comm]

end BooleanFourier


-- created on 2026-10-23
