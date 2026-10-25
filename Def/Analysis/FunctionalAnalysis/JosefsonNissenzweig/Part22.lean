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
import Theorem.Analysis.FunctionalAnalysis.JosefsonNissenzweig.Part20


section

namespace MathlibExt.Analysis.FunctionalAnalysis.JosefsonNissenzweigWanted

noncomputable def jnStableDiagonalBlocking
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {δ : ℝ} {z : ℕ → StrongDual ℝ E} (hz : JnBlockStable δ z) : JnBlocking where
  coeff n := (jnStableBlockingChain hz (Nat.log2 n)).coeff n
  norm_one n := (jnStableBlockingChain hz (Nat.log2 n)).norm_one n
  successive := by
    intro m n hmn i hi j hj
    have hlog : Nat.log2 m ≤ Nat.log2 n := jn_log2_monotone hmn.le
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hlog
    have hchain : jnStableBlockingChain hz (Nat.log2 n) =
        jnBlockingComp (jnStableBlockingChain hz (Nat.log2 m))
          (jnBlockingTailChain (jnStableStepBlocking hz) (Nat.log2 m) d) := by
      rw [hd]
      exact jn_stableBlockingChain_add hz (Nat.log2 m) d
    rw [hchain] at hj
    obtain ⟨q, hq, hjq⟩ := Finset.mem_biUnion.mp
      (jn_linearCombination_support_subset
        (jnStableBlockingChain hz (Nat.log2 m)).coeff
        ((jnBlockingTailChain (jnStableStepBlocking hz) (Nat.log2 m) d).coeff n) hj)
    have hnq : n ≤ q := jn_block_index_le_support
      (jnBlockingTailChain (jnStableStepBlocking hz) (Nat.log2 m) d) n q hq
    exact (jnStableBlockingChain hz (Nat.log2 m)).successive
      (hmn.trans_le hnq) i hi j hjq

end MathlibExt.Analysis.FunctionalAnalysis.JosefsonNissenzweigWanted
end
