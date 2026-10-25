import Mathlib
import sympy.Basic
import Theorem.v1.Atlas.Buildings.code.Reflection.DihedralRootHelpers
open Set FiniteReflectionGroups
open scoped InnerProductSpace


namespace FiniteReflectionGroups

/--
[linearReflection_unit](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Reflection/DihedralRootHelpers.lean)
-/
@[path]
private lemma linearReflection_unit
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  {e β : E}
-- given
  (he : ‖e‖ = 1) :
-- imply
  linearReflection e β = β - (2 * ⟪β, e⟫_ℝ) • e := by
-- proof
  unfold linearReflection
  have h1 : ⟪e, e⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, he, one_pow]
  rw [h1, div_one, real_inner_comm]

end FiniteReflectionGroups

namespace FiniteReflectionGroups

/--
[abs_inner_lt_one_of_not_parallel](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Reflection/DihedralRootHelpers.lean)
-/
@[path]
private lemma abs_inner_lt_one_of_not_parallel
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  {e f : E}
-- given
  (he : ‖e‖ = 1)
  (hf : ‖f‖ = 1)
  (h_not_par : ¬∃ c : ℝ, f = c • e) :
-- imply
  |⟪e, f⟫_ℝ| < 1 := by
-- proof
  rw [abs_lt]
  constructor
  ·
    by_contra h
    push Not at h
    have h1 := neg_one_le_real_inner_of_norm_eq_one he hf
    have h2 : ⟪e, f⟫_ℝ = -1 := le_antisymm h h1
    apply h_not_par
    have : ⟪e, -f⟫_ℝ = 1 := by rw [inner_neg_right, h2, neg_neg]
    exact ⟨-1, by
      rw [neg_smul, one_smul,
        (inner_eq_one_iff_of_norm_eq_one he (by rw [norm_neg, hf])).mp this,
        neg_neg]⟩
  ·
    rw [inner_lt_one_iff_real_of_norm_eq_one he hf]
    intro heq
    apply h_not_par
    exact ⟨1, by rw [heq, one_smul]⟩

end FiniteReflectionGroups


-- created on 2026-10-23
-- updated on 2026-10-24
