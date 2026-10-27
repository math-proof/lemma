import Mathlib
import Initialize.Tactic.Attr.Basic


namespace RealNumbers

/--
[real_numbers_theorem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/RealAnalysis/code/RealNumbers/Basic.lean)
-/
@[path]
lemma real_numbers_theorem
-- imply
  IsStrictOrderedRing ℝ ∧ Function.Injective (Rat.cast : ℚ → ℝ) ∧ (∀ S : Set ℝ, S.Nonempty → BddAbove S → ∃ x, IsLUB S x) :=
-- proof
  ⟨inferInstance, Rat.cast_injective, fun S hne hbdd => ⟨sSup S, Real.isLUB_sSup hne hbdd⟩⟩

end RealNumbers

namespace RealNumbers

/--
[sqrt2_exists_unique](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/RealAnalysis/code/RealNumbers/Basic.lean)
-/
@[path]
lemma sqrt2_exists_unique
-- imply
  ∃! r : ℝ, 0 < r ∧ r ^ 2 = 2 := by
-- proof
  refine ⟨Real.sqrt 2, ⟨Real.sqrt_pos_of_pos (by norm_num : (0:ℝ) < 2), ?_⟩, ?_⟩
  · rw [sq, Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  · intro y ⟨hy_pos, hy_sq⟩
    have h1 : y = Real.sqrt (y ^ 2) := by
      rw [Real.sqrt_sq hy_pos.le]
    rw [h1, hy_sq]

end RealNumbers


-- created on 2026-10-23
