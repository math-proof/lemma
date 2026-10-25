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
import Def.Analysis.FunctionalAnalysis.JosefsonNissenzweig.Part13


section

namespace MathlibExt.Analysis.FunctionalAnalysis.JosefsonNissenzweigWanted

@[simp] theorem jn_rademacher_apply (k n : ℕ) :
    jnRademacher k n = (-1 : ℝ) ^ (n / 2 ^ k) := rfl

theorem jn_rademacher_group_norm (k : ℕ) :
    ∑ i ∈ Finset.range (2 ^ (k + 1)),
        |((2 ^ (k + 1) : ℝ)⁻¹ * jnRademacher k i)| = 1 := by
  have hp : (2 ^ (k + 1) : ℝ) ≠ 0 := by positivity
  have hr : ∀ i, |jnRademacher k i| = 1 := by
    intro i
    simp only [jn_rademacher_apply, abs_pow, abs_neg, abs_one, one_pow]
  simp_rw [abs_mul, abs_inv, hr, mul_one]
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  simp [hp]

end MathlibExt.Analysis.FunctionalAnalysis.JosefsonNissenzweigWanted
end
