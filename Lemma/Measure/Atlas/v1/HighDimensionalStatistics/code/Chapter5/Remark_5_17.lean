import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.HighDimensionalStatistics.code.Chapter5.Remark_5_17
open Finset BigOperators Real Rigollet Rigollet.Chapter5


namespace Rigollet.Chapter5

/--
[l1_norm_sparse](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/Remark_5_17.lean)
-/
@[path]
lemma l1_norm_sparse
  {d : ℕ}
  {ω : Fin d → Bool}
  {R : ℝ}
  {k : ℝ}
-- given
  (hR : 0 ≤ R)
  (hk : 0 < k)
  (hcard : ((Finset.univ.filter fun i => ω i = true).card : ℝ) = k) :
-- imply
  ∑ i : Fin d, := by
-- proof
  have hRk : 0 ≤ R / k := div_nonneg hR hk.le
  have habs : ∀ i : Fin d, |sparseVec ω R k i| = sparseVec ω R k i := by
    intro i; simp only [sparseVec]; split <;> simp [abs_of_nonneg hRk]
  simp_rw [habs, sparseVec]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
    nsmul_eq_mul, hcard, mul_div_cancel₀ _ (ne_of_gt hk)]

end Rigollet.Chapter5

namespace Rigollet.Chapter5

/--
[l2_sq_sparse](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/Remark_5_17.lean)
-/
@[path]
lemma l2_sq_sparse
  {d : ℕ}
  {ω : Fin d → Bool}
  {R : ℝ}
  {k : ℝ}
-- given
  (hk : 0 < k)
  (hcard : ((Finset.univ.filter fun i => ω i = true).card : ℝ) = k) :
-- imply
  ∑ i : Fin d, (sparseVec ω R k i) ^ 2 = R ^ 2 / k := by
-- proof
  simp only [sparseVec]
  conv_lhs =>
    arg 2; ext i
    rw [show (if ω i = true then R / k else 0) ^ 2 =
      if ω i = true then (R / k) ^ 2 else 0 from by split <;> simp]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
    nsmul_eq_mul, hcard]
  rw [div_pow]
  field_simp

end Rigollet.Chapter5

namespace Rigollet.Chapter5

/--
[remark_5_17_core](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/Remark_5_17.lean)
-/
@[path]
lemma remark_5_17_core
  {k : ℝ}
  {β : ℝ}
  {R : ℝ}
-- given
  (hk : 0 < k)
  (hβ : 0 < β)
  (hkβ : k ≤ 2 / β) :
-- imply
  β / 2 * R ^ 2 ≤ R ^ 2 / k := by
-- proof
  rw [le_div_iff₀ hk]
  have h1 : k * β ≤ 2 := by
    have := mul_le_mul_of_nonneg_right hkβ hβ.le
    rwa [div_mul_cancel₀ _ (ne_of_gt hβ)] at this
  nlinarith [sq_nonneg R]
end Rigollet.Chapter5



-- created on 2026-10-23
