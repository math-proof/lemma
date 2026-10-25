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
import Def.Analysis.FunctionalAnalysis.JosefsonNissenzweig.Part14


section

namespace MathlibExt.Analysis.FunctionalAnalysis.JosefsonNissenzweigWanted

@[simp] theorem jn_blockMean_apply (p : ℕ) (hp : 0 < p)
    (f : JnBoundedSeq) (n : ℕ) :
    jnBlockMean p hp f n =
      (p : ℝ)⁻¹ * ∑ i ∈ Finset.range p, f (p * (n / p) + i) := rfl

theorem jn_blockMean_on_block (p : ℕ) (hp : 0 < p)
    (f : JnBoundedSeq) (n i : ℕ) (hi : i < p) :
    jnBlockMean p hp f (p * n + i) =
      (p : ℝ)⁻¹ * ∑ j ∈ Finset.range p, f (p * n + j) := by
  rw [jn_blockMean_apply, Nat.mul_add_div hp, Nat.div_eq_of_lt hi, Nat.add_zero]

theorem jn_blockMean_sub_sum (p : ℕ) (hp : 0 < p)
    (f : JnBoundedSeq) (n : ℕ) :
    ∑ i ∈ Finset.range p,
      (f - jnBlockMean p hp f) (p * n + i) = 0 := by
  simp only [BoundedContinuousFunction.sub_apply, Finset.sum_sub_distrib]
  have hmeans : ∑ i ∈ Finset.range p, jnBlockMean p hp f (p * n + i) =
      ∑ _i ∈ Finset.range p,
        ((p : ℝ)⁻¹ * ∑ j ∈ Finset.range p, f (p * n + j)) := by
    apply Finset.sum_congr rfl
    intro i hi
    exact jn_blockMean_on_block p hp f n i (Finset.mem_range.mp hi)
  rw [hmeans, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hp0 : (p : ℝ) ≠ 0 := by positivity
  field_simp
  ring

end MathlibExt.Analysis.FunctionalAnalysis.JosefsonNissenzweigWanted
end
