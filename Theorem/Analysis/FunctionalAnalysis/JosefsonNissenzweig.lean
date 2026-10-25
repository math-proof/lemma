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
import Def.Analysis.FunctionalAnalysis.JosefsonNissenzweig.Part2


section

namespace MathlibExt.Analysis.FunctionalAnalysis.JosefsonNissenzweigWanted

theorem jn_coeffNorm_smul (r : ℝ) (a : ℕ →₀ ℝ) :
    jnCoeffNorm (r • a) = |r| * jnCoeffNorm a := by
  classical
  by_cases hr : r = 0
  · simp [hr, jnCoeffNorm]
  · simp [jnCoeffNorm, Finsupp.sum, hr, abs_mul, Finset.mul_sum]

theorem jn_coeffNorm_add_of_disjoint {a b : ℕ →₀ ℝ}
    (h : Disjoint a.support b.support) :
    jnCoeffNorm (a + b) = jnCoeffNorm a + jnCoeffNorm b := by
  classical
  unfold jnCoeffNorm
  rw [Finsupp.sum, Finsupp.sum, Finsupp.sum, Finsupp.support_add_eq h,
    Finset.sum_union h]
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    have hib : i ∉ b.support := Finset.disjoint_left.mp h hi
    simp [Finsupp.notMem_support_iff.mp hib]
  · apply Finset.sum_congr rfl
    intro i hi
    have hia : i ∉ a.support := Finset.disjoint_right.mp h hi
    simp [Finsupp.notMem_support_iff.mp hia]

theorem jn_support_sum_subset (s : Finset ℕ) (a : ℕ → ℕ →₀ ℝ) :
    (∑ i ∈ s, a i).support ⊆ s.biUnion fun i => (a i).support := by
  classical
  intro q hq
  rw [Finset.mem_biUnion]
  by_contra hnone
  push Not at hnone
  have hz : ∀ i ∈ s, a i q = 0 := by
    intro i hi
    exact Finsupp.notMem_support_iff.mp (hnone i hi)
  apply Finsupp.mem_support_iff.mp hq
  rw [Finsupp.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro i hi
  exact hz i hi

theorem jn_coeffNorm_sum_of_pairwise_disjoint
    (s : Finset ℕ) (a : ℕ → ℕ →₀ ℝ)
    (h : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (a i).support (a j).support) :
    jnCoeffNorm (∑ i ∈ s, a i) = ∑ i ∈ s, jnCoeffNorm (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [jnCoeffNorm]
  | @insert i s hi ih =>
      have hrest : ∀ j ∈ s, ∀ k ∈ s, j ≠ k →
          Disjoint (a j).support (a k).support := by
        exact fun j hj k hk => h j (Finset.mem_insert_of_mem hj) k
          (Finset.mem_insert_of_mem hk)
      have hdis : Disjoint (a i).support (∑ j ∈ s, a j).support := by
        rw [Finset.disjoint_left]
        intro q hqi hqsum
        obtain ⟨j, hj, hqj⟩ := Finset.mem_biUnion.mp
          (jn_support_sum_subset s a hqsum)
        exact Finset.disjoint_left.mp
          (h i (Finset.mem_insert_self i s) j (Finset.mem_insert_of_mem hj)
            (by intro hij; subst j; exact hi hj)) hqi hqj
      rw [Finset.sum_insert hi, Finset.sum_insert hi,
        jn_coeffNorm_add_of_disjoint hdis, ih hrest]

theorem jn_coeffNorm_linearCombination
    (a : ℕ → ℕ →₀ ℝ)
    (ha : Pairwise fun i j => Disjoint (a i).support (a j).support)
    (b : ℕ →₀ ℝ) :
    jnCoeffNorm (Finsupp.linearCombination ℝ a b) =
      b.sum fun i t => |t| * jnCoeffNorm (a i) := by
  classical
  rw [Finsupp.linearCombination_apply]
  change jnCoeffNorm (∑ i ∈ b.support, b i • a i) =
    ∑ i ∈ b.support, |b i| * jnCoeffNorm (a i)
  rw [jn_coeffNorm_sum_of_pairwise_disjoint]
  · apply Finset.sum_congr rfl
    intro i hi
    exact jn_coeffNorm_smul (b i) (a i)
  · intro i hi j hj hij
    have hbi : b i ≠ 0 := Finsupp.mem_support_iff.mp hi
    have hbj : b j ≠ 0 := Finsupp.mem_support_iff.mp hj
    simpa [hbi, hbj] using ha hij

theorem jn_blocking_disjoint (b : JnBlocking) :
    Pairwise fun i j => Disjoint (b.coeff i).support (b.coeff j).support := by
  intro i j hij
  rw [Finset.disjoint_left]
  intro q hqi hqj
  rcases lt_or_gt_of_ne hij with hijlt | hjilt
  · exact (b.successive hijlt q hqi q hqj).false
  · exact (b.successive hjilt q hqj q hqi).false

theorem jn_blocking_support_nonempty (b : JnBlocking) (n : ℕ) :
    (b.coeff n).support.Nonempty := by
  rw [Finsupp.support_nonempty_iff]
  intro hzero
  have h := b.norm_one n
  simp [hzero, jnCoeffNorm] at h

end MathlibExt.Analysis.FunctionalAnalysis.JosefsonNissenzweigWanted
end
