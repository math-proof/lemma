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
import Theorem.Analysis.FunctionalAnalysis.JosefsonNissenzweig.Part7


section

namespace MathlibExt.Analysis.FunctionalAnalysis.JosefsonNissenzweigWanted

noncomputable def jnGroupedBlocking
    (p : ℕ) (s : ℕ → ℝ)
    (hs : ∑ i ∈ Finset.range p, |s i| = 1) : JnBlocking where
  coeff n := ∑ i ∈ Finset.range p, Finsupp.single (p * n + i) (s i)
  norm_one n := by
    rw [jn_coeffNorm_sum_of_pairwise_disjoint]
    · simpa [jnCoeffNorm] using hs
    · intro i hi j hj hij
      by_cases hsi : s i = 0
      · simp [hsi]
      by_cases hsj : s j = 0
      · simp [hsj]
      rw [Finsupp.support_single _ hsi, Finsupp.support_single _ hsj]
      simpa [Finset.disjoint_singleton] using hij
  successive := by
    intro m n hmn q hqm r hnr
    obtain ⟨i, hi, hqi⟩ := Finset.mem_biUnion.mp
      (jn_support_sum_subset (Finset.range p)
        (fun i => Finsupp.single (p * m + i) (s i)) hqm)
    obtain ⟨j, hj, hrj⟩ := Finset.mem_biUnion.mp
      (jn_support_sum_subset (Finset.range p)
        (fun j => Finsupp.single (p * n + j) (s j)) hnr)
    have hq : q = p * m + i := Finset.mem_singleton.mp
      (Finsupp.support_single_subset hqi)
    have hr : r = p * n + j := Finset.mem_singleton.mp
      (Finsupp.support_single_subset hrj)
    have hi' : i < p := Finset.mem_range.mp hi
    have hmn' : m + 1 ≤ n := Nat.succ_le_of_lt hmn
    have hleft : p * m + i < p * (m + 1) := by
      rw [Nat.mul_succ]
      omega
    have hmiddle : p * (m + 1) ≤ p * n := Nat.mul_le_mul_left p hmn'
    omega

end MathlibExt.Analysis.FunctionalAnalysis.JosefsonNissenzweigWanted
end
