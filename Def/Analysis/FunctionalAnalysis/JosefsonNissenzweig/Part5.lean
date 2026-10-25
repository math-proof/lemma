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
import Theorem.Analysis.FunctionalAnalysis.JosefsonNissenzweig.Part3


section

namespace MathlibExt.Analysis.FunctionalAnalysis.JosefsonNissenzweigWanted

noncomputable def jnSubsequenceBlocking
    (u : ℕ → ℕ) (hu : StrictMono u) : JnBlocking where
  coeff n := Finsupp.single (u n) 1
  norm_one n := by simp [jnCoeffNorm]
  successive := by
    intro m n hmn i hi j hj
    simp only [Finsupp.support_single _ one_ne_zero, Finset.mem_singleton] at hi hj
    subst i
    subst j
    exact hu hmn

end MathlibExt.Analysis.FunctionalAnalysis.JosefsonNissenzweigWanted
end
