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
import Theorem.Analysis.FunctionalAnalysis.JosefsonNissenzweig.Part6


section

namespace MathlibExt.Analysis.FunctionalAnalysis.JosefsonNissenzweigWanted

noncomputable def jnDiagonalBlocking (step : ℕ → JnBlocking) : JnBlocking where
  coeff n := (jnBlockingChain step n).coeff n
  norm_one n := (jnBlockingChain step n).norm_one n
  successive := by
    intro m n hmn i hi j hj
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hmn.le
    have hchain : jnBlockingChain step n =
        jnBlockingComp (jnBlockingChain step m) (jnBlockingTailChain step m d) := by
      rw [hd]
      exact jn_blockingChain_add step m d
    rw [hchain] at hj
    obtain ⟨q, hq, hjq⟩ := Finset.mem_biUnion.mp
      (jn_linearCombination_support_subset (jnBlockingChain step m).coeff
        ((jnBlockingTailChain step m d).coeff n) hj)
    have hnq : n ≤ q := jn_block_index_le_support
      (jnBlockingTailChain step m d) n q hq
    exact (jnBlockingChain step m).successive (hmn.trans_le hnq) i hi j hjq

end MathlibExt.Analysis.FunctionalAnalysis.JosefsonNissenzweigWanted
end
