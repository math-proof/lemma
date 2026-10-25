/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/FunctionalAnalysis/BanachLimit.lean -/

/-
Author: @toskua, Avocado
-/

import Theorem.Analysis.FunctionalAnalysis.BanachLimit.Part5
import Lemma.Filter.Any_And_Eq_1AndAll_EqAndAll_Eq
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic


namespace MathlibExt.Analysis.FunctionalAnalysis.BanachLimitTest

open Filter

open scoped BoundedContinuousFunction ContinuousLinearMap

/-- Obtain a Banach-limit witness from the proved existence theorem. -/
noncomputable def witness : (ℕ →ᵇ ℝ) →L[ℝ] ℝ :=
  Classical.choose MathlibExt.Analysis.FunctionalAnalysis.BanachLimit.banach_limit

end MathlibExt.Analysis.FunctionalAnalysis.BanachLimitTest
