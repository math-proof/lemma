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
import Def.Analysis.FunctionalAnalysis.JosefsonNissenzweig.Part8


section

namespace MathlibExt.Analysis.FunctionalAnalysis.JosefsonNissenzweigWanted

theorem jn_blockApply_diagonal
    {E : Type*} [AddCommMonoid E] [Module ℝ E]
    (step : ℕ → JnBlocking) (x : ℕ → E) (k d : ℕ) :
    jnBlockApply (jnDiagonalBlocking step) x (k + d) =
      jnBlockApply (jnBlockingTailChain step k d)
        (jnBlockApply (jnBlockingChain step k) x) (k + d) := by
  change jnBlockApply (jnBlockingChain step (k + d)) x (k + d) = _
  rw [jn_blockingChain_add, jn_blockApply_comp]

end MathlibExt.Analysis.FunctionalAnalysis.JosefsonNissenzweigWanted
end
