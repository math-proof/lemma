import Mathlib
import sympy.Basic
import Def.v1.Atlas.BooleanFunctions.code.Invariance
open Finset BigOperators MeasureTheory BooleanFourier


namespace BooleanFourier

/--
[singletonCoeffs_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/Invariance.lean)
-/
@[path]
lemma singletonCoeffs_singleton
  {n : ℕ}
  {a : Fin n → ℝ}
  {i : Fin n} :
-- imply
  singletonCoeffs a {i} = a i := by
-- proof
  simp only [singletonCoeffs]
  have h : ∃ j, ({i} : Finset (Fin n)) = {j} := ⟨i, rfl⟩
  rw [dif_pos h]
  congr 1
  exact Finset.singleton_injective h.choose_spec.symm

end BooleanFourier

namespace BooleanFourier

/--
[singletonCoeffs_non_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/Invariance.lean)
-/
@[path]
lemma singletonCoeffs_non_singleton
  {n : ℕ}
  {a : Fin n → ℝ}
  {S : Finset (Fin n)}
-- given
  (hS : ¬∃ i, S = {i}) :
-- imply
  singletonCoeffs a S = 0 := by
-- proof
  simp [singletonCoeffs, hS]

end BooleanFourier

namespace BooleanFourier

/--
[singleton_filter_eq_image](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/Invariance.lean)
-/
@[path]
lemma singleton_filter_eq_image
  {n : ℕ} :
-- imply
  (Finset.univ : Finset (Finset (Fin n))).filter (fun S => ∃ i, S = {i}) = Finset.image (fun i => ({i} : Finset (Fin n))) Finset.univ := by
-- proof
  ext S
  constructor
  · intro hS
    rw [Finset.mem_filter] at hS
    obtain ⟨_, i, rfl⟩ := hS
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  · intro hS
    rw [Finset.mem_image] at hS
    obtain ⟨i, _, rfl⟩ := hS
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, i, rfl⟩

end BooleanFourier

namespace BooleanFourier

/--
[singletonCoeffs_agree](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/Invariance.lean)
-/
@[path]
lemma singletonCoeffs_agree
  {n : ℕ}
  {a : Fin n → ℝ}
  {b : Fin n → Bool} :
-- imply
  ∑ S : Finset (Fin n), singletonCoeffs a S * ∏ i ∈ S, boolToReal (b i) = linearBooleanFunction a b := by
-- proof
  simp only [linearBooleanFunction]
  conv_lhs => rw [← Finset.sum_filter_add_sum_filter_not
    (Finset.univ : Finset (Finset (Fin n))) (fun S => ∃ i, S = {i})]
  have h_not : ∑ S ∈ (Finset.univ : Finset (Finset (Fin n))).filter
    (fun S => ¬∃ i, S = {i}),
    singletonCoeffs a S * ∏ i ∈ S, boolToReal (b i) = 0 := by
    apply Finset.sum_eq_zero
    intro S hS
    rw [Finset.mem_filter] at hS
    rw [singletonCoeffs_non_singleton a S hS.2, zero_mul]
  rw [h_not, add_zero]
  rw [singleton_filter_eq_image]
  rw [Finset.sum_image (fun i _ j _ h => Finset.singleton_injective h)]
  congr 1; ext i
  rw [singletonCoeffs_singleton, Finset.prod_singleton]

end BooleanFourier

namespace BooleanFourier

/--
[singletonCoeffs_eval](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/Invariance.lean)
-/
@[path]
lemma singletonCoeffs_eval
  {n : ℕ}
  {a : Fin n → ℝ}
  {z : Fin n → ℝ} :
-- imply
  ∑ S : Finset (Fin n), singletonCoeffs a S * ∏ i ∈ S, z i = ∑ i : Fin n, a i * z i := by
-- proof
  conv_lhs => rw [← Finset.sum_filter_add_sum_filter_not
    (Finset.univ : Finset (Finset (Fin n))) (fun S => ∃ i, S = {i})]
  have h_not : ∑ S ∈ (Finset.univ : Finset (Finset (Fin n))).filter
    (fun S => ¬∃ i, S = {i}),
    singletonCoeffs a S * ∏ i ∈ S, z i = 0 := by
    apply Finset.sum_eq_zero
    intro S hS
    rw [Finset.mem_filter] at hS
    rw [singletonCoeffs_non_singleton a S hS.2, zero_mul]
  rw [h_not, add_zero]
  rw [singleton_filter_eq_image]
  rw [Finset.sum_image (fun i _ j _ h => Finset.singleton_injective h)]
  congr 1; ext i
  rw [singletonCoeffs_singleton, Finset.prod_singleton]

end BooleanFourier

namespace BooleanFourier

/--
[invariance_principle_general](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/Invariance.lean)
-/
@[path]
lemma invariance_principle_general
  {n : ℕ}
  {f : (Fin n → Bool) → ℝ}
  {d : ℕ}
  {Ψ : ℝ → ℝ}
-- given
  (hdeg : degree f ≤ d)
  (hΨ : IsC3Bounded Ψ) :
-- imply
  |booleanExpectation f Ψ - gaussianExpectation f Ψ| ≤ (1 / 2) * (2 : ℝ) ^ ((3 : ℝ) * ↑d / 2) * hΨ.thirdDerivBound * ∑ i : Fin n, (fourierInfluence f i) ^ ((3 : ℝ) / 2) := by
-- proof
  rw [lindeberg_telescoping f Ψ]
  calc |∑ k : Fin n, (hybridExpectation f Ψ k.val - hybridExpectation f Ψ (k.val + 1))|
    ≤ ∑ k : Fin n, |hybridExpectation f Ψ k.val - hybridExpectation f Ψ (k.val + 1)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k : Fin n, ((1 / 2) * (2 : ℝ) ^ ((3 : ℝ) * ↑d / 2) * hΨ.thirdDerivBound *
      (fourierInfluence f k) ^ ((3 : ℝ) / 2)) := by
      apply Finset.sum_le_sum
      intro k _
      exact lindeberg_per_step_bound f d hdeg Ψ hΨ k
    _ = (1 / 2) * (2 : ℝ) ^ ((3 : ℝ) * ↑d / 2) * hΨ.thirdDerivBound *
      ∑ i : Fin n, (fourierInfluence f i) ^ ((3 : ℝ) / 2) := by
      rw [← Finset.mul_sum]

end BooleanFourier

namespace BooleanFourier

/--
[claim_2_2_invariance](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/Invariance.lean)
-/
@[path]
lemma claim_2_2_invariance
  {n : ℕ}
  {f : (Fin n → Bool) → ℝ}
  {τ : ℝ}
-- given
  (_hτ : 0 ≤ τ)
  (hInf : ∀ i : Fin n, fourierInfluence f i ≤ τ) :
-- imply
  ∑ i : Fin n, (fourierInfluence f i) ^ ((3 : ℝ) / 2) ≤ τ ^ ((1 : ℝ) / 2) * ∑ i : Fin n, fourierInfluence f i := by
-- proof
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hInf_nonneg : 0 ≤ fourierInfluence f i := by
    simp only [fourierInfluence]
    apply Finset.sum_nonneg
    intro S _
    split_ifs <;> positivity
  have hInf_le := hInf i
  have h_half_nonneg : (0 : ℝ) ≤ 1 / 2 := by norm_num
  calc (fourierInfluence f i) ^ ((3 : ℝ) / 2)
    = (fourierInfluence f i) ^ (1 + (1 : ℝ) / 2) := by ring_nf
    _ = (fourierInfluence f i) ^ (1 : ℝ) * (fourierInfluence f i) ^ ((1 : ℝ) / 2) := by
      obtain h | h := eq_or_lt_of_le hInf_nonneg
      · simp [← h, Real.zero_rpow (by norm_num : (1 : ℝ) + 2⁻¹ ≠ 0),
        Real.zero_rpow (by norm_num : (1 : ℝ) ≠ 0),
        Real.zero_rpow (by norm_num : (2 : ℝ)⁻¹ ≠ 0)]
      · exact Real.rpow_add h 1 (1/2)
    _ = fourierInfluence f i * (fourierInfluence f i) ^ ((1 : ℝ) / 2) := by
      rw [Real.rpow_one]
    _ ≤ fourierInfluence f i * τ ^ ((1 : ℝ) / 2) := by
      apply mul_le_mul_of_nonneg_left
      · exact Real.rpow_le_rpow hInf_nonneg hInf_le h_half_nonneg
      · exact hInf_nonneg
    _ = τ ^ ((1 : ℝ) / 2) * fourierInfluence f i := by ring

end BooleanFourier

namespace BooleanFourier

/--
[fourierInfluence_eq_influenceReal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/Invariance.lean)
-/
@[path]
lemma fourierInfluence_eq_influenceReal
  {n : ℕ}
  {f : (Fin n → Bool) → ℝ}
  {i : Fin n} :
-- imply
  fourierInfluence f i = influenceReal f i := by
-- proof
  rw [influenceReal_eq_sum_fourierCoeff_sq]
  simp only [fourierInfluence]
  rw [← Finset.sum_filter]

end BooleanFourier

namespace BooleanFourier

/--
[sum_fourierInfluence_eq_totalInfluenceReal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/Invariance.lean)
-/
@[path]
lemma sum_fourierInfluence_eq_totalInfluenceReal
  {n : ℕ}
  {f : (Fin n → Bool) → ℝ} :
-- imply
  ∑ i : Fin n, fourierInfluence f i = totalInfluenceReal f := by
-- proof
  simp_rw [fourierInfluence_eq_influenceReal]
  rfl

end BooleanFourier

namespace BooleanFourier

/--
[totalInfluenceReal_le_degree_mul_varianceReal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/Invariance.lean)
-/
@[path]
lemma totalInfluenceReal_le_degree_mul_varianceReal
  {n : ℕ}
  {f : (Fin n → Bool) → ℝ}
  {d : ℕ}
-- given
  (hdeg : degree f ≤ d) :
-- imply
  totalInfluenceReal f ≤ (d : ℝ) * varianceReal f := by
-- proof
  rw [totalInfluenceReal_eq_sum_card_fourierCoeff_sq]
  unfold varianceReal
  rw [Finset.sum_filter]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro S _
  by_cases hS : S = ∅
  · simp [hS]
  · simp only [ne_eq, hS, not_false_eq_true, ite_true]
    by_cases hcoeff : fourierCoeff f S = 0
    · simp [hcoeff]
    · have hsq : (0 : ℝ) ≤ fourierCoeff f S ^ 2 := sq_nonneg _
      apply mul_le_mul_of_nonneg_right _ hsq
      have h1 : S.card ≤ degree f := by
        unfold degree
        apply Finset.le_sup
        simp [hcoeff]
      exact_mod_cast h1.trans hdeg

end BooleanFourier

namespace BooleanFourier

/--
[invariance_principle_corollary](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/Invariance.lean)
-/
@[path]
lemma invariance_principle_corollary
  {C : ℝ}
  {ε : ℝ}
  {d : ℕ}
-- given
  (hC : C > 0)
  (hε : ε > 0) :
-- imply
  ∃ τ > 0, ∀ (n : ℕ) (f : (Fin n → Bool) → ℝ), degree f ≤ d → (∀ i : Fin n, fourierInfluence f i ≤ τ) → varianceReal f ≤ C → ∀ (Ψ : ℝ → ℝ) (hΨ : IsC3Bounded Ψ), hΨ.thirdDerivBound ≤ C → |booleanExpectation f Ψ - gaussianExpectation f Ψ| ≤ ε := by
-- proof
  set K : ℝ := (1 / 2) * (2 : ℝ) ^ ((3 : ℝ) * ↑d / 2) * C ^ 2 * ↑d + 1
  have hK_pos : K > 0 := by positivity
  refine ⟨(ε / K) ^ 2, by positivity, ?_⟩
  intro n f hdeg hInf hVar Ψ hΨ hΨ_bound
  have h_sum_infl : ∑ i : Fin n, fourierInfluence f i ≤ ↑d * C := by
    rw [sum_fourierInfluence_eq_totalInfluenceReal]
    exact (totalInfluenceReal_le_degree_mul_varianceReal f d hdeg).trans
      (mul_le_mul_of_nonneg_left hVar (Nat.cast_nonneg' d))
  have h_claim22 := claim_2_2_invariance f ((ε / K) ^ 2)
    (by positivity : (0 : ℝ) ≤ (ε / K) ^ 2) hInf
  have h_rpow_sq : ((ε / K) ^ 2) ^ ((1 : ℝ) / 2) = ε / K := by
    have hpos : (0 : ℝ) < ε / K := by positivity
    rw [← Real.rpow_natCast (ε / K) 2]
    rw [← Real.rpow_mul (le_of_lt hpos)]
    norm_num
  have hsum_bound : ∑ i : Fin n, (fourierInfluence f i) ^ ((3 : ℝ) / 2) ≤
    (ε / K) * (↑d * C) := by
    calc ∑ i : Fin n, (fourierInfluence f i) ^ ((3 : ℝ) / 2)
      ≤ ((ε / K) ^ 2) ^ ((1 : ℝ) / 2) * ∑ i : Fin n, fourierInfluence f i := h_claim22
      _ ≤ ((ε / K) ^ 2) ^ ((1 : ℝ) / 2) * (↑d * C) := by
        apply mul_le_mul_of_nonneg_left h_sum_infl
        positivity
      _ = (ε / K) * (↑d * C) := by rw [h_rpow_sq]
  have h_rhs_le_eps : (1 / 2) * (2 : ℝ) ^ ((3 : ℝ) * ↑d / 2) * hΨ.thirdDerivBound *
    ∑ i : Fin n, (fourierInfluence f i) ^ ((3 : ℝ) / 2) ≤ ε := by
    have h_bound_C : hΨ.thirdDerivBound ≤ C := hΨ_bound
    calc (1 / 2) * (2 : ℝ) ^ ((3 : ℝ) * ↑d / 2) * hΨ.thirdDerivBound *
      ∑ i : Fin n, (fourierInfluence f i) ^ ((3 : ℝ) / 2)
      ≤ (1 / 2) * (2 : ℝ) ^ ((3 : ℝ) * ↑d / 2) * C *
        ((ε / K) * (↑d * C)) := by
        have h1 : (0 : ℝ) ≤ (1 / 2) * (2 : ℝ) ^ ((3 : ℝ) * ↑d / 2) := by positivity
        have h2 : hΨ.thirdDerivBound * ∑ i : Fin n, (fourierInfluence f i) ^ ((3 : ℝ) / 2) ≤
          C * (ε / K * (↑d * C)) := by
          calc hΨ.thirdDerivBound * ∑ i : Fin n, (fourierInfluence f i) ^ ((3 : ℝ) / 2)
            ≤ C * ∑ i : Fin n, (fourierInfluence f i) ^ ((3 : ℝ) / 2) := by
              apply mul_le_mul_of_nonneg_right h_bound_C
              apply Finset.sum_nonneg; intro i _
              exact Real.rpow_nonneg (by
                simp only [fourierInfluence]
                exact Finset.sum_nonneg (fun S _ => by split_ifs <;> positivity)) _
            _ ≤ C * (ε / K * (↑d * C)) := by
              apply mul_le_mul_of_nonneg_left hsum_bound (le_of_lt hC)
        nlinarith
      _ = ((1 / 2) * (2 : ℝ) ^ ((3 : ℝ) * ↑d / 2) * C ^ 2 * ↑d) * (ε / K) := by ring
      _ ≤ (K - 1) * (ε / K) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        simp only [K]; linarith
      _ ≤ K * (ε / K) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        linarith
      _ = ε := by field_simp
  exact (invariance_principle_general f d hdeg Ψ hΨ).trans h_rhs_le_eps
end BooleanFourier



-- created on 2026-10-23
