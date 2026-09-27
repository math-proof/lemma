import Mathlib.Topology.MetricSpace.Cauchy
import sympy.stats.frozen_invariant_law
import sympy.Basic
import Lemma.Real.Norm.le.Sum_Abs
import Lemma.StochasticVec.IsClosed
import Lemma.Real.Tendsto.of.Gt_0
import Lemma.UniformExponentialMixing.Sum_AbsSub.le.MulMulCMixExpMulNeg2.of.Ge_0.StochasticVec.StochasticVec.In_ActorBox
open Filter Topology


@[main]
private lemma main
  {S : Type*} [Fintype S] [DecidableEq S]
  {d : ℕ}
  {r : ℝ}
  {Q : EuclideanVec d → Matrix S S ℝ}
  {θ : EuclideanVec d}
-- given
  (h₀ : θ ∈ actor_box d r)
  (hMix : UniformExponentialMixing r Q) :
-- imply
  ∃ μ, StochasticVec μ ∧ ∀ t, 0 ≤ t → hMix.semigroup.toFun θ t μ = μ := by
-- proof
  have := hMix.hQ.nonempty
  let T := hMix.semigroup.toFun θ
  let μ₀ : S → ℝ := uniform_distribution
  let x : ℕ → S → ℝ := fun n => T n μ₀
  let b : ℕ → ℝ := fun n => hMix.cMix * Real.exp (-hMix.γ * n) * 2
  have hb : Tendsto b atTop (𝓝 0) := (Real.Tendsto.of.Gt_0 hMix.γ_pos _ 2).comp tendsto_natCast_atTop_atTop
  have hshift : ∀ (s : ℝ) (n : ℕ), 0 ≤ s → dist (T (n + s) μ₀) (x n) ≤ b n := by
    intro s n hs
    have h := UniformExponentialMixing.Sum_AbsSub.le.MulMulCMixExpMulNeg2.of.Ge_0.StochasticVec.StochasticVec.In_ActorBox h₀ (hMix.semigroup.preserves_simplex θ h₀ μ₀ inferInstance s hs) (inferInstance : StochasticVec μ₀) (Nat.cast_nonneg n) hMix
    simp only [T, x, b, hMix.semigroup.map_add' θ n s (Nat.cast_nonneg n) hs, ContinuousLinearMap.comp_apply]
    rw [dist_eq_norm]
    exact (Real.Norm.le.Sum_Abs _).trans (by simpa using h)
  have hcauchy : CauchySeq x := by
    refine cauchySeq_of_le_tendsto_0' b (fun n m hnm => ?_) hb
    rw [dist_comm]
    simpa [x] using hshift (m - n : ℝ) n (by simp [hnm])
  obtain ⟨μ, hμ⟩ := cauchySeq_tendsto_of_complete hcauchy
  refine ⟨μ, (StochasticVec.IsClosed).mem_of_tendsto hμ (Eventually.of_forall fun n => hMix.semigroup.preserves_simplex θ h₀ μ₀ inferInstance n (Nat.cast_nonneg n)), fun t ht => ?_⟩
  have h₁ : Tendsto (fun n => T t (x n)) atTop (𝓝 (T t μ)) := ((T t).continuous.tendsto μ).comp hμ
  have h₂ : Tendsto (fun n => T t (x n)) atTop (𝓝 μ) := by
    have e : ∀ n : ℕ, T t (x n) = T (n + t) μ₀ := fun n => by
      show hMix.semigroup.toFun θ t (hMix.semigroup.toFun θ n μ₀) = hMix.semigroup.toFun θ (n + t) μ₀
      rw [add_comm, hMix.semigroup.map_add' θ t n ht (Nat.cast_nonneg n)]
      rfl
    simp only [e]
    refine tendsto_iff_dist_tendsto_zero.2 (squeeze_zero (fun _ => dist_nonneg) (fun n => (dist_triangle _ (x n) μ).trans (add_le_add (hshift t n ht) le_rfl)) ?_)
    simpa using hb.add (tendsto_iff_dist_tendsto_zero.1 hμ)
  exact tendsto_nhds_unique h₁ h₂


-- created on 2026-09-26
