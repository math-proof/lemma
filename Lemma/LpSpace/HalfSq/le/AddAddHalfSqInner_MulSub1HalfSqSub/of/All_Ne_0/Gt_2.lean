import Lemma.LpSpace.HasDerivAtPowNormAddSmulSub.of.Ge_2
import Lemma.Real.HasDerivAtSumMulMulPowAbsAddMulSub.of.Ge_2
import Lemma.LpSpace.SumMulPowAbsSquare.le.MulPowNormSquareNorm.of.Gt_2
import Lemma.Real.Le_AddAddDiv2.of.All_Le.All_HasDerivAt.ContinuousOn.All_HasDerivAt.ContinuousOn
import Lemma.LpSpace.ContinuousHalfSq.of.Ge_1
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
open Finset LpSpace Real Set


@[main]
private lemma main
  {p d : ℕ}
  {x y : LpSpace p d}
-- given
  (h₀ : 2 < p)
  (h₁ : ∀ t ∈ Icc (0 : ℝ) 1, x + t • (y - x) ≠ 0) :
-- imply
  half_sq y ≤ half_sq x + inner ℝ (half_sq' x).toL2 (y - x).toL2 + (p - 1) * half_sq (y - x) := by
-- proof
  have : Fact (1 ≤ (p : ENNReal)) := ⟨by exact_mod_cast (by omega : 1 ≤ p)⟩
  have hp : (2 : ℝ) < p := by exact_mod_cast h₀
  have hp0 : (p : ℝ) ≠ 0 := by positivity
  have hp2 : ((p - 2 : ℕ) : ℝ) = p - 2 := by push_cast [Nat.cast_sub h₀.le]; ring
  let N : ℝ → ℝ := fun t => ‖x + t • (y - x)‖ ^ p
  let N' : ℝ → ℝ := fun t => ∑ i, p * |x i + t * (y i - x i)| ^ (p - 2) * (x i + t * (y i - x i)) * (y i - x i)
  let N'' : ℝ → ℝ := fun t => ∑ i, p * (p - 1) * |x i + t * (y i - x i)| ^ (p - 2) * (y i - x i) ^ 2
  let φ : ℝ → ℝ := fun t => half_sq (x + t • (y - x))
  let φ' : ℝ → ℝ := fun t => (p : ℝ)⁻¹ * N t ^ (2 / (p : ℝ) - 1) * N' t
  let φ'' : ℝ → ℝ := fun t => (p : ℝ)⁻¹ * ((2 / (p : ℝ) - 1) * N t ^ (2 / (p : ℝ) - 2) * N' t ^ 2 + N t ^ (2 / (p : ℝ) - 1) * N'' t)
  let M : ℝ := (p - 1) * ‖y - x‖ ^ 2
  have hN : ∀ t, HasDerivAt N (N' t) t := fun t => HasDerivAtPowNormAddSmulSub.of.Ge_2 h₀.le
  have hN' : ∀ t, HasDerivAt N' (N'' t) t := fun t => HasDerivAtSumMulMulPowAbsAddMulSub.of.Ge_2 h₀.le
  have hNpos : ∀ t ∈ Icc (0 : ℝ) 1, 0 < N t := fun t ht => pow_pos (norm_pos_iff.2 (h₁ t ht)) p
  have hNc : Continuous N := continuous_iff_continuousAt.2 fun t => (hN t).continuousAt
  have hN'c : Continuous N' := continuous_iff_continuousAt.2 fun t => (hN' t).continuousAt
  have hφ : φ = fun t => 1 / 2 * N t ^ (2 / (p : ℝ)) := by
    funext t
    simp only [φ, N, half_sq]
    rw [← Real.rpow_natCast _ p, ← Real.rpow_mul (norm_nonneg _), show (p : ℝ) * (2 / p) = 2 by field_simp, Real.rpow_two]
  have hc₀ : ContinuousOn φ (Icc 0 1) :=
    ((ContinuousHalfSq.of.Ge_1 (by omega : 1 ≤ p)).comp (by fun_prop : Continuous fun t : ℝ => x + t • (y - x))).continuousOn
  have hd₁ : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt φ (φ' t) t := fun t ht => by
    rw [hφ]
    refine (((hN t).rpow_const (Or.inl (hNpos t (Ioo_subset_Icc_self ht)).ne')).const_mul (1 / 2)).congr_deriv ?_
    simp only [φ']
    field_simp
  have hc₂ : ContinuousOn φ' (Icc 0 1) :=
    (continuousOn_const.mul (hNc.continuousOn.rpow_const fun t ht => Or.inl (hNpos t ht).ne')).mul hN'c.continuousOn
  have hd₃ : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt φ' (φ'' t) t := fun t ht => by
    refine ((((hN t).rpow_const (Or.inl (hNpos t (Ioo_subset_Icc_self ht)).ne')).const_mul (p : ℝ)⁻¹).mul (hN' t)).congr_deriv ?_
    simp only [φ'']
    rw [show (2 : ℝ) / p - 1 - 1 = 2 / p - 2 by ring]
    ring
  have hb₄ : ∀ t ∈ Ioo (0 : ℝ) 1, φ'' t ≤ M := fun t ht => by
    have ht' := Ioo_subset_Icc_self ht
    have hz : 0 < ‖x + t • (y - x)‖ := norm_pos_iff.2 (h₁ t ht')
    have hS := SumMulPowAbsSquare.le.MulPowNormSquareNorm.of.Gt_2 (z := x + t • (y - x)) (v := y - x) h₀
    have hN'' : N'' t ≤ p * (p - 1) * ‖x + t • (y - x)‖ ^ (p - 2) * ‖y - x‖ ^ 2 := by
      simpa [N''] using hS
    have hNz : N t ^ (2 / (p : ℝ) - 1) * ‖x + t • (y - x)‖ ^ (p - 2) = 1 := by
      simp only [N]
      rw [← Real.rpow_natCast _ p, ← Real.rpow_mul (norm_nonneg _), ← Real.rpow_natCast _ (p - 2), hp2,
        ← Real.rpow_add hz, show (p : ℝ) * (2 / p - 1) + (p - 2) = 0 by field_simp; ring, Real.rpow_zero]
    have hA : (p : ℝ)⁻¹ * ((2 / (p : ℝ) - 1) * N t ^ (2 / (p : ℝ) - 2) * N' t ^ 2) ≤ 0 := by
      have h21 : 2 / (p : ℝ) - 1 ≤ 0 := by
        rw [sub_nonpos, div_le_one (by positivity)]
        linarith
      exact mul_nonpos_of_nonneg_of_nonpos (by positivity)
        (mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg h21 (Real.rpow_nonneg (hNpos t ht').le _)) (sq_nonneg _))
    calc
      _ = (p : ℝ)⁻¹ * ((2 / (p : ℝ) - 1) * N t ^ (2 / (p : ℝ) - 2) * N' t ^ 2) + (p : ℝ)⁻¹ * N t ^ (2 / (p : ℝ) - 1) * N'' t := by
        simp only [φ'']
        ring
      _ ≤ 0 + (p : ℝ)⁻¹ * N t ^ (2 / (p : ℝ) - 1) * (p * (p - 1) * ‖x + t • (y - x)‖ ^ (p - 2) * ‖y - x‖ ^ 2) :=
        add_le_add hA (mul_le_mul_of_nonneg_left hN'' (by positivity))
      _ = ((p : ℝ)⁻¹ * p) * (p - 1) * (N t ^ (2 / (p : ℝ) - 1) * ‖x + t • (y - x)‖ ^ (p - 2)) * ‖y - x‖ ^ 2 := by ring
      _ = M := by rw [hNz, inv_mul_cancel₀ hp0]; ring
  have hG := Le_AddAddDiv2.of.All_Le.All_HasDerivAt.ContinuousOn.All_HasDerivAt.ContinuousOn hc₀ hd₁ hc₂ hd₃ hb₄
  have e₀ : (‖x‖ ^ p) ^ ((2 : ℝ) / p - 1) = ‖x‖ ^ (2 - (p : ℝ)) := by
    rw [← Real.rpow_natCast _ p, ← Real.rpow_mul (norm_nonneg _)]
    congr 1
    field_simp
  have hφ'0 : φ' 0 = inner ℝ (half_sq' x).toL2 (y - x).toL2 := by
    simp only [φ', N, N', zero_smul, add_zero, zero_mul]
    rw [e₀]
    simp only [toL2, half_sq', PiLp.inner_apply, WithLp.ofLp_toLp, RCLike.inner_apply, conj_trivial, WithLp.ofLp_sub, Pi.sub_apply]
    rw [Finset.mul_sum]
    refine sum_congr rfl fun i _ => ?_
    rw [← Real.rpow_natCast _ (p - 2), hp2]
    field_simp
  have e₁ : φ 1 = half_sq y := by simp [φ]
  have e₂ : φ 0 = half_sq x := by simp [φ]
  rw [e₁, e₂, hφ'0] at hG
  calc
    _ ≤ _ := hG
    _ = _ := by
      simp only [M, half_sq]
      ring


-- created on 2026-09-26