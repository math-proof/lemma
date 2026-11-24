module
public import Mathlib.Analysis.Normed.Module.DoubleDual
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Group.Quotient
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.Analysis.Normed.Module.RCLike.Extend
public import Mathlib.Analysis.Normed.Operator.Mul
public import Mathlib.Tactic.NormNum
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import Theorem.Analysis.FunctionalAnalysis.BanachLimit.Part5
public import Theorem.Filter.Any_And_Eq_1AndAll_EqAndAll_Eq
public import Theorem.Set.Any_All_Any_All_LtNormSubOrHasUniformL1LowerBound.of.IsBounded_Range
public import Theorem.Analysis.FunctionalAnalysis.RosenthalL1.Part13
public import Def.Analysis.FunctionalAnalysis.JosefsonNissenzweig.Part13


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/FunctionalAnalysis/JosefsonNissenzweig.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/
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
