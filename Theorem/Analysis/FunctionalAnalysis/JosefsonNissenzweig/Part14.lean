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
import Def.Analysis.FunctionalAnalysis.JosefsonNissenzweig.Part15


section

namespace MathlibExt.Analysis.FunctionalAnalysis.JosefsonNissenzweigWanted

theorem jn_partialSum_add (d : JnBoundedSeq) (n r : ℕ) :
    jnPartialSum d (n + r) =
      jnPartialSum d n + ∑ i ∈ Finset.range r, d (n + i) := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [Nat.add_succ, jnPartialSum, ih, Finset.sum_range_succ]
      ring

theorem jn_partialSum_blocks (p : ℕ) (hp : 0 < p)
    (f : JnBoundedSeq) (n : ℕ) :
    jnPartialSum (f - jnBlockMean p hp f) (p * n) = 0 := by
  induction n with
  | zero => simp [jnPartialSum]
  | succ n ih =>
      rw [Nat.mul_succ, jn_partialSum_add, ih, zero_add,
        jn_blockMean_sub_sum]

end MathlibExt.Analysis.FunctionalAnalysis.JosefsonNissenzweigWanted
end
