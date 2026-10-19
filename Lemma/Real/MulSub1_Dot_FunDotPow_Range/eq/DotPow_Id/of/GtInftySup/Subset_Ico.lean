import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import sympy.vector.Basic
import sympy.concrete.sup
import sympy.core.function
open Finset


/--
Generalized advantage estimation (Schulman et al., arXiv 1506.02438, Eq. (16)):
for bounded temporal-difference residuals δ and γ, ℓ ∈ [0, 1), the exponentially weighted average
(1 - ℓ) * ∑' k, ℓ ^ k * ∑ i ∈ range (k + 1), γ ^ i * δ[t + i] of the k-step advantage estimates
(∑ i ∈ range (k + 1), γ ^ i * δ[t + i] is the (k + 1)-step estimate) equals the closed form
(γ * ℓ) ** Stack[i](i) @ δ[t:] = ∑' i, (γ * ℓ) ^ i * δ[t + i].
This connects the weighted average of k-step estimates with the closed form A[t] used in
generalized_advantage_estimate of the policy gradient.
-/
@[path]
private lemma main
  {γ ℓ : ℝ}
  {δ : Fun ℕ ℝ}
  {t : ℕ}
-- given
  (h₀ : ({γ, ℓ} : Set ℝ) ⊆ Set.Ico 0 1)
  (h₁ : sup[t] |δ[t]| < ∞) :
-- imply
  (1 - ℓ) * ((ℓ ^ (id : ℕ → ℕ)) @ fun k ↦ (γ ^ range (k + 1)) @ δ[t:]) =
    ((γ * ℓ) ^ (id : ℕ → ℕ)) @ δ[t:] := by
-- proof
  obtain ⟨hγ0, hγ1⟩ : γ ∈ Set.Ico 0 1 := h₀ (by simp)
  obtain ⟨hℓ0, hℓ1⟩ : ℓ ∈ Set.Ico 0 1 := h₀ (by simp)
  obtain ⟨B, hB⟩ := h₁
  have hB' : ∀ n, |δ[n]| ≤ B := fun n => hB ⟨n, rfl⟩
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB' 0)
  have hc0 : 0 ≤ γ * ℓ := mul_nonneg hγ0 hℓ0
  have hc1 : γ * ℓ < 1 := (mul_le_of_le_one_left hℓ0 hγ1.le).trans_lt hℓ1
  have hf : Summable fun i : ℕ => ‖(γ * ℓ) ^ i * δ[t + i]‖ := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun i => ?_)
      ((summable_geometric_of_lt_one hc0 hc1).mul_right B)
    rw [norm_mul, norm_pow, Real.norm_of_nonneg hc0]
    exact mul_le_mul_of_nonneg_left (hB' _) (pow_nonneg hc0 _)
  have hg : Summable fun j : ℕ => ‖ℓ ^ j‖ := by
    simpa [norm_pow, Real.norm_of_nonneg hℓ0] using summable_geometric_of_lt_one hℓ0 hℓ1
  have key := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hf hg
  have e1 : ∀ k, ∑ ij ∈ antidiagonal k, ((γ * ℓ) ^ ij.1 * δ[t + ij.1]) * ℓ ^ ij.2 =
      ℓ ^ k * ∑ i ∈ range (k + 1), γ ^ i * δ[t + i] := by
    intro k
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have : ℓ ^ k = ℓ ^ i * ℓ ^ (k - i) := by rw [← pow_add, Nat.add_sub_cancel' hik]
    rw [this, mul_pow]
    ring
  simp only [e1] at key
  rw [tsum_geometric_of_lt_one hℓ0 hℓ1] at key
  have hL :
      (ℓ ^ (id : ℕ → ℕ)) @ (fun k ↦ (γ ^ range (k + 1)) @ δ[t:]) =
        ∑' k, ℓ ^ k * ∑ i ∈ range (k + 1), γ ^ i * δ[t + i] := by
    simp_rw [FinsetPow.dot_eq]
    simp [Dot.dot, Function.hPow_apply, Fun.getSliceFrom_apply]
  have hR :
      ((γ * ℓ) ^ (id : ℕ → ℕ)) @ δ[t:] =
        ∑' i, (γ * ℓ) ^ i * δ[t + i] := by
    simp [Dot.dot, Function.hPow_apply, Fun.getSliceFrom_apply]
  rw [hL, hR, ← key]
  have : (1 - ℓ) ≠ 0 := (sub_pos.mpr hℓ1).ne'
  field_simp


-- created on 2023-04-08
