module
public import Theorem.Analysis.FunctionalAnalysis.BanachLimit.Part5
public import Theorem.Filter.Any_And_Eq_1AndAll_EqAndAll_Eq
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/FunctionalAnalysis/BanachLimit.lean -/
/-
Author: @toskua, Avocado
-/
namespace MathlibExt.Analysis.FunctionalAnalysis.BanachLimitTest

open Filter

open scoped BoundedContinuousFunction ContinuousLinearMap

/-- Obtain a Banach-limit witness from the proved existence theorem. -/
noncomputable def witness : (ℕ →ᵇ ℝ) →L[ℝ] ℝ :=
  Classical.choose MathlibExt.Analysis.FunctionalAnalysis.BanachLimit.banach_limit

end MathlibExt.Analysis.FunctionalAnalysis.BanachLimitTest
