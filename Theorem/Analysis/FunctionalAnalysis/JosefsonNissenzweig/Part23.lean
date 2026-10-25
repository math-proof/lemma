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
import Def.Analysis.FunctionalAnalysis.JosefsonNissenzweig.Part24


section

namespace MathlibExt.Analysis.FunctionalAnalysis.JosefsonNissenzweigWanted

@[simp] theorem jn_l1SignFunctional_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {c : ℝ} (hc : 0 < c) {x : ℕ → E} (hx : JnL1Lower c x) (m i : ℕ) :
    jnL1SignFunctional hc hx m
        ⟨x i, Submodule.subset_span (Set.mem_range_self i)⟩ = jnRademacher i m := by
  simp only [jnL1SignFunctional, LinearMap.mkContinuous_apply, jnL1SignLinearMap]
  rw [show ⟨x i, Submodule.subset_span (Set.mem_range_self i)⟩ =
      jnL1Basis hc hx i by
    ext
    simp only [jnL1Basis, Module.Basis.coe_span_apply]]
  exact (jnL1Basis hc hx).constr_basis ℝ _ i

end MathlibExt.Analysis.FunctionalAnalysis.JosefsonNissenzweigWanted
end
