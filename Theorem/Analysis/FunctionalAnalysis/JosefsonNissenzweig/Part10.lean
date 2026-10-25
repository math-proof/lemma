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
import Def.Analysis.FunctionalAnalysis.JosefsonNissenzweig.Part11


section

namespace MathlibExt.Analysis.FunctionalAnalysis.JosefsonNissenzweigWanted

@[simp] theorem jn_blockApply_wholeGroup
    {E : Type*} [AddCommMonoid E] [Module ℝ E]
    (p : ℕ) (hp : 0 < p) (u : ℕ → ℕ) (hu : StrictMono u)
    (x : ℕ → E) (n : ℕ) :
    jnBlockApply (jnWholeGroupBlocking p hp u hu) x n =
      x (jnWholeGroupIndex p u n) := by
  exact jn_blockApply_subsequence _ _ _ _

end MathlibExt.Analysis.FunctionalAnalysis.JosefsonNissenzweigWanted
end
