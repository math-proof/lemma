/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/FunctionalAnalysis/JosefsonNissenzweig.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Module.RCLike.Extend
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Tactic.NormNum
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Theorem.Analysis.FunctionalAnalysis.BanachLimit.Part5
import Lemma.Filter.Any_And_Eq_1AndAll_EqAndAll_Eq
import Lemma.Set.Any_All_Any_All_LtNormSubOrHasUniformL1LowerBound.of.IsBounded_Range
import Theorem.Analysis.FunctionalAnalysis.RosenthalL1.Part13
import Theorem.Analysis.FunctionalAnalysis.JosefsonNissenzweig.Part12


section

namespace MathlibExt.Analysis.FunctionalAnalysis.JosefsonNissenzweigWanted

noncomputable def jnRademacherBlocking (k : ℕ) : JnBlocking :=
  jnGroupedBlocking (2 ^ (k + 1))
    (fun i => (2 ^ (k + 1) : ℝ)⁻¹ * jnRademacher k i)
    (jn_rademacher_group_norm k)

noncomputable def jnBlockMean (p : ℕ) (hp : 0 < p)
    (f : JnBoundedSeq) : JnBoundedSeq :=
  BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
    (fun n => (p : ℝ)⁻¹ * ∑ i ∈ Finset.range p, f (p * (n / p) + i))
    ‖f‖ (fun n => by
      have hpR : 0 < (p : ℝ) := by exact_mod_cast hp
      have hsum : ‖∑ i ∈ Finset.range p, f (p * (n / p) + i)‖ ≤
          (p : ℝ) * ‖f‖ := by
        calc
          ‖∑ i ∈ Finset.range p, f (p * (n / p) + i)‖ ≤
              ∑ i ∈ Finset.range p, ‖f (p * (n / p) + i)‖ := norm_sum_le _ _
          _ ≤ ∑ _i ∈ Finset.range p, ‖f‖ := by
            apply Finset.sum_le_sum
            intro i hi
            exact f.norm_coe_le_norm _
          _ = (p : ℝ) * ‖f‖ := by
            simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      rw [norm_mul, Real.norm_eq_abs, abs_inv, abs_of_pos hpR]
      calc
        (p : ℝ)⁻¹ * ‖∑ i ∈ Finset.range p, f (p * (n / p) + i)‖ ≤
            (p : ℝ)⁻¹ * ((p : ℝ) * ‖f‖) :=
          mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hpR.le)
        _ = ‖f‖ := by field_simp)

end MathlibExt.Analysis.FunctionalAnalysis.JosefsonNissenzweigWanted
end
