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
public import Theorem.Analysis.FunctionalAnalysis.JosefsonNissenzweig.Part2


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/FunctionalAnalysis/JosefsonNissenzweig.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/
section

namespace MathlibExt.Analysis.FunctionalAnalysis.JosefsonNissenzweigWanted

noncomputable def jnBlockingComp (a b : JnBlocking) : JnBlocking where
  coeff n := Finsupp.linearCombination ℝ a.coeff (b.coeff n)
  norm_one n := by
    rw [jn_coeffNorm_linearCombination a.coeff (jn_blocking_disjoint a)]
    simp_rw [a.norm_one, mul_one]
    exact b.norm_one n
  successive := by
    intro m n hmn q hqm r hnr
    obtain ⟨i, hi, hqi⟩ := Finset.mem_biUnion.mp
      (jn_linearCombination_support_subset a.coeff (b.coeff m) hqm)
    obtain ⟨j, hj, hrj⟩ := Finset.mem_biUnion.mp
      (jn_linearCombination_support_subset a.coeff (b.coeff n) hnr)
    exact a.successive (b.successive hmn i hi j hj) q hqi r hrj

end MathlibExt.Analysis.FunctionalAnalysis.JosefsonNissenzweigWanted
end
