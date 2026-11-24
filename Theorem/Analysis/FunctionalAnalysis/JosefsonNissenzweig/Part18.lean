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
public import Def.Analysis.FunctionalAnalysis.JosefsonNissenzweig.Part19


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/FunctionalAnalysis/JosefsonNissenzweig.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/
section

namespace MathlibExt.Analysis.FunctionalAnalysis.JosefsonNissenzweigWanted

theorem jn_block_preserves_l1_lower
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {c : ℝ} {x : ℕ → E} (hx : JnL1Lower c x) (b : JnBlocking) :
    JnL1Lower c (jnBlockApply b x) := by
  intro a
  have h := hx (Finsupp.linearCombination ℝ b.coeff a)
  have hnorm : (Finsupp.linearCombination ℝ b.coeff a).sum (fun _ t => |t|) =
      a.sum (fun _ t => |t|) := by
    change jnCoeffNorm (Finsupp.linearCombination ℝ b.coeff a) = jnCoeffNorm a
    rw [jn_coeffNorm_linearCombination b.coeff (jn_blocking_disjoint b)]
    simp_rw [b.norm_one, mul_one]
    rfl
  rw [Finsupp.linearCombination_linearCombination ℝ x b.coeff a] at h
  rw [hnorm] at h
  exact h

theorem jn_blockApply_eval_lt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (b : JnBlocking) (z : ℕ → StrongDual ℝ E) (x : E) (n : ℕ) {ε : ℝ}
    (h : ∀ i ∈ (b.coeff n).support, ‖z i x‖ < ε) :
    ‖jnBlockApply b z n x‖ < ε := by
  rw [jnBlockApply, Finsupp.linearCombination_apply, Finsupp.sum]
  simp_rw [sum_apply, smul_apply, smul_eq_mul]
  calc
    ‖∑ i ∈ (b.coeff n).support, b.coeff n i * z i x‖ ≤
        ∑ i ∈ (b.coeff n).support, ‖b.coeff n i * z i x‖ := norm_sum_le _ _
    _ = ∑ i ∈ (b.coeff n).support, |b.coeff n i| * ‖z i x‖ := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [norm_mul, Real.norm_eq_abs]
    _ < ∑ i ∈ (b.coeff n).support, |b.coeff n i| * ε := by
      apply Finset.sum_lt_sum_of_nonempty (jn_blocking_support_nonempty b n)
      intro i hi
      exact mul_lt_mul_of_pos_left (h i hi)
        (abs_pos.mpr (Finsupp.mem_support_iff.mp hi))
    _ = ε := by
      rw [← Finset.sum_mul, ← Finsupp.sum, ← jnCoeffNorm, b.norm_one, one_mul]

end MathlibExt.Analysis.FunctionalAnalysis.JosefsonNissenzweigWanted
end
