import Mathlib
import sympy.Basic
import Def.v1.Atlas.ProjectionTheory.code.BKTLemma2
open Finset MultiplicativeConvolution
open scoped BigOperators


namespace MultiplicativeConvolution

/--
[norm_mulConv_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/BKTLemma2.lean)
-/
@[path]
lemma norm_mulConv_le
  [Fintype G]
  [Group G]
  {f g : G → ℂ}
  {a : G} :
-- imply
  ‖mulConv f g a‖ ≤ l2Norm f * l2Norm g := by
-- proof
  unfold mulConv l2Norm
  have hreindex : ∑ b : G, ‖g (a * b⁻¹)‖ ^ 2 = ∑ b : G, ‖g b‖ ^ 2 :=
    Fintype.sum_equiv (mulInvEquiv a) _ _ (fun _ => rfl)
  calc ‖∑ b : G, f b * g (a * b⁻¹)‖
    ≤ ∑ b : G, ‖f b * g (a * b⁻¹)‖ := norm_sum_le _ _
    _ = ∑ b : G, ‖f b‖ * ‖g (a * b⁻¹)‖ := by
      congr 1; ext b; exact norm_mul _ _
    _ ≤ Real.sqrt (∑ b : G, ‖f b‖ ^ 2) * Real.sqrt (∑ b : G, ‖g (a * b⁻¹)‖ ^ 2) :=
      Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ = Real.sqrt (∑ b : G, ‖f b‖ ^ 2) * Real.sqrt (∑ b : G, ‖g b‖ ^ 2) := by
      rw [hreindex]

end MultiplicativeConvolution

namespace MultiplicativeConvolution

/--
[linftyNorm_mulConv_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/BKTLemma2.lean)
-/
@[path]
lemma linftyNorm_mulConv_le
  [Fintype G]
  [Group G]
  {f g : G → ℂ} :
-- imply
  (⨆ a : G, ‖mulConv f g a‖) ≤ l2Norm f * l2Norm g := by
-- proof
  apply ciSup_le
  exact norm_mulConv_le f g

end MultiplicativeConvolution


-- created on 2026-10-23
