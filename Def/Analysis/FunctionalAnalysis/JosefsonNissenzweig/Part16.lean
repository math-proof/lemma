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
import Theorem.Analysis.FunctionalAnalysis.JosefsonNissenzweig.Part14


section

namespace MathlibExt.Analysis.FunctionalAnalysis.JosefsonNissenzweigWanted

noncomputable def jnBlockPrimitive (p : ℕ) (hp : 0 < p)
    (f : JnBoundedSeq) : JnBoundedSeq :=
  let d := f - jnBlockMean p hp f
  BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
    (jnPartialSum d) ((p : ℝ) * ‖d‖) (fun n => by
      let q := n / p
      let r := n % p
      have hr : r < p := Nat.mod_lt n hp
      have hn : p * q + r = n := by
        simpa [q, r, Nat.mul_comm] using Nat.div_add_mod n p
      have hsum := jn_partialSum_add d (p * q) r
      rw [jn_partialSum_blocks p hp f q] at hsum
      have heq : jnPartialSum d n = ∑ i ∈ Finset.range r, d (p * q + i) := by
        rw [← hn, hsum, zero_add]
      rw [heq]
      calc
        ‖∑ i ∈ Finset.range r, d (p * q + i)‖ ≤
            ∑ i ∈ Finset.range r, ‖d (p * q + i)‖ := norm_sum_le _ _
        _ ≤ ∑ _i ∈ Finset.range r, ‖d‖ := by
          apply Finset.sum_le_sum
          intro i hi
          exact d.norm_coe_le_norm _
        _ = (r : ℝ) * ‖d‖ := by
          simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        _ ≤ (p : ℝ) * ‖d‖ := by
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg d)
          exact_mod_cast hr.le)

end MathlibExt.Analysis.FunctionalAnalysis.JosefsonNissenzweigWanted
end
