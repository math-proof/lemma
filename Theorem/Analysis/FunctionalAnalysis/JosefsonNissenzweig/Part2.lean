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
import Def.Analysis.FunctionalAnalysis.JosefsonNissenzweig.Part3


section

namespace MathlibExt.Analysis.FunctionalAnalysis.JosefsonNissenzweigWanted

theorem jn_blockFirst_strictMono (b : JnBlocking) :
    StrictMono (jnBlockFirst b) := by
  intro m n hmn
  exact b.successive hmn _ (Finset.min'_mem _ _) _ (Finset.min'_mem _ _)

theorem jn_block_index_le_support (b : JnBlocking) (n i : ℕ)
    (hi : i ∈ (b.coeff n).support) : n ≤ i := by
  exact (jn_blockFirst_strictMono b).id_le n |>.trans (Finset.min'_le _ _ hi)

theorem jn_linearCombination_support_subset
    (a : ℕ → ℕ →₀ ℝ) (b : ℕ →₀ ℝ) :
    (Finsupp.linearCombination ℝ a b).support ⊆
      b.support.biUnion fun i => (a i).support := by
  classical
  rw [Finsupp.linearCombination_apply]
  change (∑ i ∈ b.support, b i • a i).support ⊆ _
  intro q hq
  obtain ⟨i, hi, hqi⟩ := Finset.mem_biUnion.mp
    (jn_support_sum_subset b.support (fun i => b i • a i) hq)
  refine Finset.mem_biUnion.mpr ⟨i, hi, ?_⟩
  by_contra hnot
  apply Finsupp.mem_support_iff.mp hqi
  simp [Finsupp.notMem_support_iff.mp hnot]

end MathlibExt.Analysis.FunctionalAnalysis.JosefsonNissenzweigWanted
end
