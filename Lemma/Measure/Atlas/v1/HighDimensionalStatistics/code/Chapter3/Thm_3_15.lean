import Mathlib
import sympy.Basic
import Def.v1.Atlas.HighDimensionalStatistics.code.Chapter3.Thm_3_15.Part2
open Real MeasureTheory Chapter3


namespace Chapter3

/--
[trigDesignMatrix_eq_trigBasis](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter3/Thm_3_15.lean)
-/
@[path]
lemma trigDesignMatrix_eq_trigBasis
  {n M : ℕ}
  {i : Fin n}
  {j : Fin M}
-- given
  (hn : 0 < n) :
-- imply
  trigDesignMatrix n M i j = trigBasis (j.val + 1) ((i : ℝ) / (n : ℝ)) := by
-- proof
  simp only [trigDesignMatrix, trigBasis]
  have hj1 : j.val + 1 ≠ 0 := Nat.succ_ne_zero _
  simp only [hj1, ↓reduceIte]
  by_cases hj1eq : j.val + 1 = 1
  ·
    have hj0 : j.val = 0 := by omega
    simp [hj0]
  ·
    have hjge1 : j.val ≥ 1 := by omega
    simp only [hj1eq, ↓reduceIte]
    by_cases hjmod : j.val = 0
    · omega
    · simp only [show j.val ≠ 0 from hjmod]
      by_cases heven : (j.val + 1) % 2 = 0
      ·
        simp only [heven, ↓reduceIte]
        have hj_odd : j.val % 2 = 1 := by omega
        simp only [hj_odd, ↓reduceIte]
        congr 1
        have : (j.val + 1) / 2 = (j.val + 1) / 2 := rfl
        ring
      ·
        have hodd : (j.val + 1) % 2 = 1 := by omega
        simp only [show ¬((j.val + 1) % 2 = 0) from by omega, ↓reduceIte]
        have hj_even : j.val % 2 = 0 := by omega
        have hj_ne0 : ¬(j.val = 0) := hjmod
        simp only [hj_even]
        push_cast
        ring

end Chapter3

namespace Chapter3

/--
[empirical_norm_eq_sum_sq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter3/Thm_3_15.lean)
-/
@[path]
lemma empirical_norm_eq_sum_sq
  {n M : ℕ}
  {θ : Fin M → ℝ}
-- given
  (hn : 0 < n)
  (hM : M ≤ n - 1) :
-- imply
  (1 / (n : ℝ)) * ∑ i : Fin n, (∑ j : Fin M, θ j * trigBasis (j.val + 1) ((i : ℝ) / (n : ℝ))) ^ 2 = ∑ j : Fin M, θ j ^ 2 := by
-- proof
  have hΦ : ∀ i : Fin n,
    ∑ j : Fin M, θ j * trigBasis (j.val + 1) ((i : ℝ) / (n : ℝ)) =
    ∑ j : Fin M, trigDesignMatrix n M i j * θ j := by
    intro i
    congr 1; ext j
    rw [trigDesignMatrix_eq_trigBasis n M hn i j]; ring
  simp_rw [hΦ]
  set Φ := trigDesignMatrix n M
  have hmv : ∀ i, ∑ j : Fin M, Φ i j * θ j = (Φ.mulVec θ) i := by
    intro i; simp [Matrix.mulVec, dotProduct]
  simp_rw [hmv]
  have hdot_sum : ∑ i : Fin n, (Φ.mulVec θ i) ^ 2 =
    dotProduct (Φ.mulVec θ) (Φ.mulVec θ) := by
    simp [dotProduct, sq]
  rw [hdot_sum]
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec]
  rw [lemma_3_13 n M hn hM]
  rw [Matrix.vecMul_smul, Matrix.vecMul_one]
  rw [smul_dotProduct, smul_eq_mul]
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  field_simp
  simp [dotProduct, sq]

end Chapter3

namespace Chapter3

/--
[trigBasis_L2_orthonormal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter3/Thm_3_15.lean)
-/
@[path]
lemma trigBasis_L2_orthonormal
  {j j' : ℕ}
-- given
  (hj : 0 < j)
  (hj' : 0 < j') :
-- imply
  ∫ x in Set.Icc (0 : ℝ) 1, trigBasis j x * trigBasis j' x = if j = j' then 1 else 0 :=
-- proof
  trigBasis_orthonormal j j' hj hj'

end Chapter3

namespace Chapter3

/--
[L2_norm_eq_sum_sq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter3/Thm_3_15.lean)
-/
@[path]
lemma L2_norm_eq_sum_sq
  {M : ℕ}
  {θ : Fin M → ℝ} :
-- imply
  L2normSq (fun x => ∑ j : Fin M, θ j * trigBasis (j.val + 1) x) = ∑ j : Fin M, θ j ^ 2 := by
-- proof
  unfold L2normSq
  have hcont : Continuous (fun x => ∑ j : Fin M, θ j * trigBasis (j.val + 1) x) :=
    continuous_finset_sum _ (fun j _ => continuous_const.mul
      (by unfold trigBasis; split_ifs <;> fun_prop))
  have hint : IntegrableOn (fun x =>
    (∑ j : Fin M, θ j * trigBasis (j.val + 1) x) ^ 2) (Set.Icc 0 1) :=
    (hcont.pow 2).continuousOn.integrableOn_compact isCompact_Icc
  simp_rw [sq, Finset.sum_mul_sum]
  have hint_prod : ∀ j j' : Fin M,
    IntegrableOn (fun x => θ j * trigBasis (j.val + 1) x * (θ j' * trigBasis (j'.val + 1) x))
      (Set.Icc 0 1) :=
    fun j j' => ((continuous_const.mul
      (by unfold trigBasis; split_ifs <;> fun_prop)).mul
      (continuous_const.mul
      (by unfold trigBasis; split_ifs <;> fun_prop))).continuousOn.integrableOn_compact isCompact_Icc
  rw [integral_finset_sum _ (fun j _ =>
    integrable_finset_sum _ (fun j' _ => hint_prod j j'))]
  congr 1; ext j
  rw [integral_finset_sum _ (fun j' _ => hint_prod j j')]
  simp_rw [show ∀ (j' : Fin M) (x : ℝ),
    θ j * trigBasis (j.val + 1) x * (θ j' * trigBasis (j'.val + 1) x) =
    θ j * θ j' * (trigBasis (j.val + 1) x * trigBasis (j'.val + 1) x)
    from by intros; ring]
  simp_rw [integral_const_mul]
  simp_rw [trigBasis_L2_orthonormal _ _ (Nat.succ_pos _) (Nat.succ_pos _)]
  simp_rw [Nat.succ_inj, Fin.val_injective.eq_iff]
  simp

end Chapter3

namespace Chapter3

/--
[ORT_L2_eq_empirical_normSq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter3/Thm_3_15.lean)
-/
@[path]
lemma ORT_L2_eq_empirical_normSq
  {n M : ℕ}
  {θ : Fin M → ℝ}
-- given
  (hn : 0 < n)
  (hM : M ≤ n - 1) :
-- imply
  L2normSq (fun x => ∑ j : Fin M, θ j * trigBasis (j.val + 1) x) = (1 / (n : ℝ)) * ∑ i : Fin n, (∑ j : Fin M, θ j * trigBasis (j.val + 1) ((i : ℝ) / (n : ℝ))) ^ 2 := by
-- proof
  rw [L2_norm_eq_sum_sq, empirical_norm_eq_sum_sq n M hn hM]

end Chapter3

namespace Chapter3

/--
[trigLinComb_eq_mulVec](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter3/Thm_3_15.lean)
-/
@[path]
lemma trigLinComb_eq_mulVec
  {n M : ℕ}
  {θ : Fin M → ℝ}
  {i : Fin n}
-- given
  (hn : 0 < n) :
-- imply
  trigLinComb M θ ((i : ℝ) / (n : ℝ)) = (trigDesignMatrix n M).mulVec θ i := by
-- proof
  simp only [trigLinComb, Matrix.mulVec, dotProduct]
  congr 1; ext j
  rw [trigDesignMatrix_eq_trigBasis n M hn i j]; ring

end Chapter3

namespace Chapter3

/--
[finset_range_eq_fin_sum](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter3/Thm_3_15.lean)
-/
@[path]
lemma finset_range_eq_fin_sum
  {M : ℕ}
  {θstar : ℕ → ℝ}
  {x : ℝ} :
-- imply
  ∑ j ∈ Finset.range M, θstar j * trigBasis (j + 1) x = ∑ j : Fin M, θstar j.val * trigBasis (j.val + 1) x := by
-- proof
  rw [← Finset.sum_range (fun j => θstar j * trigBasis (j + 1) x)]

end Chapter3

namespace Chapter3

/--
[empirical_diff_eq_coeff_sq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter3/Thm_3_15.lean)
-/
@[path]
lemma empirical_diff_eq_coeff_sq
  {n M : ℕ}
  {θ₁ θ₂ : Fin M → ℝ}
-- given
  (hn : 0 < n)
  (hM : M ≤ n - 1) :
-- imply
  (1 / (n : ℝ)) * ∑ i : Fin n, (∑ j : Fin M, θ₁ j * trigBasis (j.val + 1) ((i : ℝ) / (n : ℝ)) - ∑ j : Fin M, θ₂ j * trigBasis (j.val + 1) ((i : ℝ) / (n : ℝ))) ^ 2 = ∑ j : Fin M, (θ₁ j - θ₂ j) ^ 2 := by
-- proof
  have hdiff : ∀ i : Fin n,
    ∑ j : Fin M, θ₁ j * trigBasis (j.val + 1) ((i : ℝ) / (n : ℝ)) -
    ∑ j : Fin M, θ₂ j * trigBasis (j.val + 1) ((i : ℝ) / (n : ℝ)) =
    ∑ j : Fin M, (θ₁ j - θ₂ j) * trigBasis (j.val + 1) ((i : ℝ) / (n : ℝ)) := by
    intro i
    rw [← Finset.sum_sub_distrib]
    congr 1; ext j; ring
  simp_rw [hdiff]
  exact empirical_norm_eq_sum_sq n M hn hM (θ₁ - θ₂)

end Chapter3

namespace Chapter3

/--
[trigBasis_col_sq_sum](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter3/Thm_3_15.lean)
-/
@[path]
lemma trigBasis_col_sq_sum
  {n M : ℕ}
  {j : Fin M}
-- given
  (hn : 0 < n)
  (hM : M ≤ n - 1) :
-- imply
  ∑ i : Fin n, (trigBasis (j.val + 1) ((i : ℝ) / (n : ℝ))) ^ 2 = (n : ℝ) := by
-- proof
  have h_eq : ∀ i : Fin n,
    trigBasis (j.val + 1) ((i : ℝ) / (n : ℝ)) = trigDesignMatrix n M i j :=
    fun i => (trigDesignMatrix_eq_trigBasis n M hn i j).symm
  simp_rw [h_eq]
  have h_ort := lemma_3_13 n M hn hM
  have h_entry := congr_fun (congr_fun h_ort j) j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply,
    Matrix.one_apply, smul_eq_mul] at h_entry
  simp only [if_true] at h_entry
  simp_rw [sq]
  linarith

end Chapter3

namespace Chapter3

/--
[fourier_tail_L2_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter3/Thm_3_15.lean)
-/
@[path]
lemma fourier_tail_L2_bound
  {M : ℕ}
  {β Q : ℝ}
  {θstar : ℕ → ℝ}
-- given
  (hM : 0 < M)
  (hβ : 1/2 < β)
  (hQ : 0 < Q)
  (hSobolev : ∀ (K : ℕ), ∑ j : Fin K, (sobolevCoeff β (j.val + 1)) ^ 2 * (θstar j.val) ^ 2 ≤ Q) :
-- imply
  L2normSq (fun x => (∑' j, θstar j * trigBasis (j + 1) x) - ∑ j ∈ Finset.range M, θstar j * trigBasis (j + 1) x) ≤ Q * (M : ℝ) ^ (-(2 * β)) := by
-- proof
  have hβ_pos : 0 < β := by linarith
  have hRange : ∀ K, ∑ i ∈ Finset.range K,
    (sobolevCoeff β (↑i + 1)) ^ 2 * (θstar ↑i) ^ 2 ≤ Q := by
    intro K
    rw [← Fin.sum_univ_eq_sum_range]
    exact hSobolev K
  have hnn : ∀ i, 0 ≤ (sobolevCoeff β (↑i + 1)) ^ 2 * (θstar ↑i) ^ 2 :=
    fun i => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hSummable : Summable (fun j => (sobolevCoeff β (↑j + 1)) ^ 2 * (θstar ↑j) ^ 2) :=
    summable_of_sum_range_le hnn hRange
  have hBound : ∑' j, (sobolevCoeff β (↑j + 1)) ^ 2 * (θstar ↑j) ^ 2 ≤ Q :=
    tsum_le_of_sum_range_le hnn hRange
  have h_tail : Summable (fun j : ℕ => (θstar (j + 1)) ^ 2) := by
    have hsumshift : Summable (fun j =>
      (sobolevCoeff β (j + 1 + 1)) ^ 2 * (θstar (j + 1)) ^ 2) :=
      hSummable.comp_injective (fun a b h => by omega)
    exact Summable.of_nonneg_of_le (fun j => sq_nonneg _)
      (fun j => by
        nlinarith [sq_nonneg (θstar (j + 1)),
          sobolev_weight_ge_one β hβ_pos (j + 1) (by omega)])
      hsumshift
  have hSqSum : Summable (fun j : ℕ => (θstar j) ^ 2) :=
    (summable_nat_add_iff 1).mp h_tail
  show L2normSq _ ≤ _
  simp only [L2normSq]
  have hAbsSum : Summable θstar := by
    exact summable_of_sobolev hβ θstar ⟨hSummable, hBound⟩
  rw [parseval_truncation_L2_error θstar M hSqSum hAbsSum]
  have hM_pos : (0 : ℝ) < (M : ℝ) := Nat.cast_pos.mpr hM
  have hMinv_pos : (0 : ℝ) < (M : ℝ) ^ (-(2 * β)) := rpow_pos_of_pos hM_pos _
  have h_term : ∀ (j : ↑(Set.Ici M)),
    (θstar ↑j) ^ 2 ≤ (M : ℝ) ^ (-(2 * β)) *
      ((sobolevCoeff β (↑(↑j : ℕ) + 1)) ^ 2 * (θstar ↑j) ^ 2) := by
    intro ⟨j, hj⟩
    simp only [Set.mem_Ici] at hj
    suffices h1 : 1 ≤ (M : ℝ) ^ (-(2 * β)) *
      (sobolevCoeff β (j + 1)) ^ 2 by
      nlinarith [sq_nonneg (θstar j)]
    rw [rpow_neg hM_pos.le, inv_mul_eq_div,
      le_div_iff₀ (rpow_pos_of_pos hM_pos _)]
    simp only [one_mul]
    exact sobolev_weight_ge_rpow β hβ_pos M j hj
  calc ∑' (j : ↑(Set.Ici M)), (θstar ↑j) ^ 2
    _ ≤ ∑' (j : ↑(Set.Ici M)), (M : ℝ) ^ (-(2 * β)) *
      ((sobolevCoeff β (↑(↑j : ℕ) + 1)) ^ 2 * (θstar ↑j) ^ 2) :=
      Summable.tsum_le_tsum h_term (hSqSum.subtype _)
        ((Summable.mul_left _ hSummable).subtype _)
    _ = (M : ℝ) ^ (-(2 * β)) *
      ∑' (j : ↑(Set.Ici M)),
        ((sobolevCoeff β (↑(↑j : ℕ) + 1)) ^ 2 * (θstar ↑j) ^ 2) :=
      tsum_mul_left
    _ ≤ (M : ℝ) ^ (-(2 * β)) *
      ∑' j : ℕ, (sobolevCoeff β (j + 1)) ^ 2 * (θstar j) ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ hMinv_pos.le
      exact Summable.tsum_subtype_le _ _
        (fun j => mul_nonneg (sq_nonneg _) (sq_nonneg _)) hSummable
    _ ≤ (M : ℝ) ^ (-(2 * β)) * Q :=
      mul_le_mul_of_nonneg_left hBound hMinv_pos.le
    _ = Q * (M : ℝ) ^ (-(2 * β)) := mul_comm ..

end Chapter3

namespace Chapter3

/--
[approx_error_integrableOn](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter3/Thm_3_15.lean)
-/
@[path]
lemma approx_error_integrableOn
  {M : ℕ}
  {β Q : ℝ}
  {f : ℝ → ℝ}
  {θstar : ℕ → ℝ}
-- given
  (_hM : 0 < M)
  (_hβ : 0 < β)
  (_hQ : 0 < Q)
  (_hθstar : ∀ j, θstar j = fourierCoeff f j)
  (_hSobolev : ∀ (K : ℕ), ∑ j : Fin K, (sobolevCoeff β (j.val + 1)) ^ 2 * (θstar j.val) ^ 2 ≤ Q)
  (hf_meas : Measurable f)
  (hf_sq_int : IntegrableOn (fun x => f x ^ 2) (Set.Icc 0 1)) :
-- imply
  IntegrableOn (fun x => ((∑ j ∈ Finset.range M, θstar j * trigBasis (j + 1) x) - f x) ^ 2) (Set.Icc 0 1) := by
-- proof
  have continuous_trigBasis : ∀ j : ℕ, Continuous (trigBasis j) := by
    intro j; unfold trigBasis; split_ifs <;> fun_prop
  have hsum_cont : Continuous (fun x =>
    ∑ j ∈ Finset.range M, θstar j * trigBasis (j + 1) x) :=
    continuous_finset_sum _ (fun j _ => continuous_const.mul (continuous_trigBasis _))
  have hdiff_meas : Measurable (fun x =>
    (∑ j ∈ Finset.range M, θstar j * trigBasis (j + 1) x) - f x) :=
    hsum_cont.measurable.sub hf_meas
  have hbound : ∀ x : ℝ,
    ((∑ j ∈ Finset.range M, θstar j * trigBasis (j + 1) x) - f x) ^ 2 ≤
    2 * ((∑ j ∈ Finset.range M, θstar j * trigBasis (j + 1) x) ^ 2 + f x ^ 2) := by
    intro x; nlinarith [sq_nonneg ((∑ j ∈ Finset.range M, θstar j * trigBasis (j + 1) x) + f x)]
  have hsum_sq_int : IntegrableOn (fun x =>
    (∑ j ∈ Finset.range M, θstar j * trigBasis (j + 1) x) ^ 2) (Set.Icc 0 1) :=
    (hsum_cont.pow 2).continuousOn.integrableOn_compact isCompact_Icc
  have hbnd_int : IntegrableOn (fun x =>
    2 * ((∑ j ∈ Finset.range M, θstar j * trigBasis (j + 1) x) ^ 2 + f x ^ 2))
    (Set.Icc 0 1) := (hsum_sq_int.add hf_sq_int).const_mul 2
  exact Integrable.mono' hbnd_int
    ((hdiff_meas.pow_const 2).aestronglyMeasurable.restrict)
    (Filter.Eventually.of_forall (fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hbound x))

end Chapter3

namespace Chapter3

/--
[L2normSq_add_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter3/Thm_3_15.lean)
-/
@[path]
lemma L2normSq_add_le
-- given
  (g h : ℝ → ℝ)
  (hg : IntegrableOn (fun x => g x ^ 2) (Set.Icc 0 1))
  (hh : IntegrableOn (fun x => h x ^ 2) (Set.Icc 0 1)) :
-- imply
  L2normSq (fun x => g x + h x) ≤ 2 * (L2normSq g + L2normSq h) := by
-- proof
  unfold L2normSq; simp only
  have key : ∀ x : ℝ, (g x + h x) ^ 2 ≤ 2 * (g x ^ 2 + h x ^ 2) := by
    intro x; nlinarith [sq_nonneg (g x - h x)]
  have hgh_int : IntegrableOn (fun x => g x ^ 2 + h x ^ 2) (Set.Icc 0 1) := hg.add hh
  have step1 : ∫ x in Set.Icc (0:ℝ) 1, (g x + h x) ^ 2 ≤
    ∫ x in Set.Icc (0:ℝ) 1, 2 * (g x ^ 2 + h x ^ 2) := by
    apply integral_mono_of_nonneg
    · exact ae_of_all _ (fun x => sq_nonneg (g x + h x))
    · exact hgh_int.const_mul 2
    · exact ae_of_all _ key
  have step2a : ∫ x in Set.Icc (0:ℝ) 1, 2 * (g x ^ 2 + h x ^ 2) =
    2 * (∫ x in Set.Icc (0:ℝ) 1, (g x ^ 2 + h x ^ 2)) := by
    rw [show (fun x => 2 * (g x ^ 2 + h x ^ 2)) = (fun x => (2 : ℝ) • (g x ^ 2 + h x ^ 2))
      from by ext x; simp [mul_comm]]
    rw [integral_smul (2 : ℝ)]
    simp [smul_eq_mul]
  have step2b : (∫ x in Set.Icc (0:ℝ) 1, (g x ^ 2 + h x ^ 2)) =
    (∫ x in Set.Icc (0:ℝ) 1, g x ^ 2) + (∫ x in Set.Icc (0:ℝ) 1, h x ^ 2) :=
    integral_add hg hh
  linarith

end Chapter3

namespace Chapter3

/--
[thm_3_15_rate_computation](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter3/Thm_3_15.lean)
-/
@[path]
lemma thm_3_15_rate_computation
  {n : ℕ}
  {β : ℝ}
  {M : ℕ}
  {σ : ℝ}
-- given
  (hn : 0 < n)
  (hβ_pos : 0 < β)
  (hβ_lower : β ≥ (1 + Real.sqrt 5) / 4)
  (_hM_pos : 0 < M)
  (hM_choice : (n : ℝ) ^ ((1 : ℝ) / (2 * β + 1)) ≤ (M : ℝ) ∧ (M : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / (2 * β + 1)) + 1)
  (_hσ : 0 < σ) :
-- imply
  ∃ (C' : ℝ), 0 < C' ∧ ∀ (δ : ℝ), 0 < δ → δ ≤ 1 → (M : ℝ) ^ (-(2 * β)) + (n : ℝ) ^ (1 - 2 * β) + ((M : ℝ) + σ ^ 2 * Real.log (1 / δ)) / (n : ℝ) ≤ C' * (n : ℝ) ^ (-(2 * β) / (2 * β + 1)) + C' * σ ^ 2 * Real.log (1 / δ) / (n : ℝ) := by
-- proof
  refine ⟨4, by norm_num, ?_⟩
  intro δ hδ_pos hδ_le
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hn_ge1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h2β1_pos : (0 : ℝ) < 2 * β + 1 := by linarith
  have hMn_lb := hM_choice.1
  have hMn_ub := hM_choice.2
  set rate := (n : ℝ) ^ (-(2 * β) / (2 * β + 1)) with rate_def
  set tail := σ ^ 2 * Real.log (1 / δ) / (n : ℝ) with tail_def
  have h1 : (M : ℝ) ^ (-(2 * β)) ≤ rate := by
    have hn1 : 0 < (n : ℝ) ^ ((1:ℝ) / (2*β+1)) := rpow_pos_of_pos hn_pos _
    calc (M : ℝ) ^ (-(2*β))
      ≤ ((n : ℝ) ^ ((1:ℝ) / (2*β+1))) ^ (-(2*β)) :=
        rpow_le_rpow_of_nonpos hn1 hMn_lb (by linarith)
      _ = rate := by rw [rate_def, ← rpow_mul hn_pos.le]; ring_nf
  have h2 : (n : ℝ) ^ (1 - 2 * β) ≤ rate := by
    rw [rate_def]
    apply rpow_le_rpow_of_exponent_le hn_ge1
    rw [le_div_iff₀ h2β1_pos]
    have h4β : 4 * β - 1 ≥ Real.sqrt 5 := by linarith
    have h4βsq : (4 * β - 1) ^ 2 ≥ (Real.sqrt 5) ^ 2 :=
      sq_le_sq' (by linarith [Real.sqrt_nonneg 5]) h4β
    rw [Real.sq_sqrt (show (5:ℝ) ≥ 0 by norm_num)] at h4βsq
    nlinarith [h4βsq]
  have h3 : (M : ℝ) / (n : ℝ) ≤ 2 * rate := by
    have step1 : (M : ℝ) / (n : ℝ) ≤ ((n : ℝ) ^ ((1:ℝ) / (2*β+1)) + 1) / (n : ℝ) :=
      div_le_div_of_nonneg_right hMn_ub hn_pos.le
    rw [add_div] at step1
    have key1 : (n : ℝ) ^ ((1:ℝ) / (2*β+1)) / (n : ℝ) = rate := by
      rw [rate_def, div_eq_mul_inv, ← rpow_neg_one (n : ℝ), ← rpow_add hn_pos]
      congr 1; field_simp; ring
    have key2 : 1 / (n : ℝ) ≤ rate := by
      rw [one_div, ← rpow_neg_one (n : ℝ), rate_def]
      apply rpow_le_rpow_of_exponent_le hn_ge1
      rw [neg_div, neg_le_neg_iff, div_le_one h2β1_pos]
      linarith
    linarith [step1, key1, key2]
  have hsplit : ((M : ℝ) + σ ^ 2 * Real.log (1 / δ)) / (n : ℝ) =
    (M : ℝ) / (n : ℝ) + tail := by rw [tail_def, add_div]
  rw [hsplit]
  have htail_nn : 0 ≤ tail := by
    rw [tail_def]
    exact div_nonneg (mul_nonneg (sq_nonneg σ)
      (Real.log_nonneg (by rw [le_div_iff₀ hδ_pos]; linarith))) hn_pos.le
  have hrhs : 4 * (n : ℝ) ^ (-(2 * β) / (2 * β + 1)) +
    4 * σ ^ 2 * Real.log (1 / δ) / (n : ℝ) = 4 * rate + 4 * tail := by
    rw [rate_def, tail_def]; ring
  rw [hrhs]
  linarith

end Chapter3

namespace Chapter3

/--
[expectation_from_exponential_tail_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter3/Thm_3_15.lean)
-/
@[path]
lemma expectation_from_exponential_tail_bound
  [MeasurableSpace Ω]
  {μ : Measure Ω}
  [IsProbabilityMeasure μ]
  {X : Ω → ℝ}
  {A B : ℝ}
-- given
  (hX_meas : Measurable X)
  (_hX_nn : ∀ ω, 0 ≤ X ω)
  (_hA : 0 ≤ A)
  (hB : 0 < B)
  (htail : ∀ δ : ℝ, 0 < δ → δ ≤ 1 → μ {ω | X ω ≤ A + B * Real.log (1 / δ)} ≥ ENNReal.ofReal (1 - δ)) :
-- imply
  ∫ ω, X ω ∂μ ≤ A + B := by
-- proof
  by_cases hInt : Integrable X μ
  ·
    have step1 : ∫ ω, X ω ∂μ = ∫ ω, (X ω - A) ∂μ + A := by
      rw [integral_sub hInt (integrable_const A), integral_const]
      simp [Measure.real, measure_univ]
    rw [step1]
    suffices h : ∫ ω, (X ω - A) ∂μ ≤ B by linarith
    have hIntXA : Integrable (fun ω => X ω - A) μ := hInt.sub (integrable_const A)
    have hIntMax : Integrable (fun ω => max (X ω - A) 0) μ := hIntXA.pos_part
    have hMeasMax : AEStronglyMeasurable (fun ω => max (X ω - A) 0) μ :=
      ((hX_meas.sub measurable_const).max measurable_const).aestronglyMeasurable
    have hlint : ∫⁻ ω, ENNReal.ofReal (max (X ω - A) 0) ∂μ ≤ ENNReal.ofReal B := by
      rw [lintegral_eq_lintegral_meas_lt μ
        (by filter_upwards with ω; exact le_max_right _ _)
        ((hX_meas.sub measurable_const).max measurable_const).aemeasurable]
      calc ∫⁻ (t : ℝ) in Set.Ioi 0, μ {a | t < max (X a - A) 0}
        ≤ ∫⁻ (t : ℝ) in Set.Ioi 0, ENNReal.ofReal (Real.exp ((-1/B) * t)) := by
          apply lintegral_mono_ae
          filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
          simp only [Set.mem_Ioi] at ht
          have hset : {a | t < max (X a - A) 0} = {a | A + t < X a} := by
            ext a; simp only [Set.mem_setOf_eq, max_def]; split_ifs with h
            · constructor; intro h2; linarith; intro h2; linarith
            · push Not at h; constructor; intro h2; linarith; intro h2; linarith
          rw [hset]
          set δ := Real.exp ((-1/B) * t)
          have hδ_pos : 0 < δ := exp_pos _
          have hδ_le : δ ≤ 1 := exp_le_one_iff.mpr
            (mul_nonpos_of_nonpos_of_nonneg
              (div_nonpos_of_nonpos_of_nonneg (by norm_num) hB.le) ht.le)
          have hTail' := htail δ hδ_pos hδ_le
          have key : A + B * Real.log (1 / δ) = A + t := by
            congr 1; rw [one_div, Real.log_inv, Real.log_exp]; field_simp
          rw [key] at hTail'
          have hms : MeasurableSet {ω | X ω ≤ A + t} := hX_meas measurableSet_Iic
          rw [show {a | A + t < X a} = {ω | X ω ≤ A + t}ᶜ from by
            ext ω; simp [not_le]]
          rw [measure_compl hms (measure_ne_top μ _), measure_univ]
          calc (1 : ENNReal) - μ {ω | X ω ≤ A + t}
            ≤ 1 - ENNReal.ofReal (1 - δ) := tsub_le_tsub_left hTail' _
            _ = ENNReal.ofReal δ := by
              rw [show (1:ENNReal) = ENNReal.ofReal 1 from by simp]
              rw [← ENNReal.ofReal_sub 1 (by linarith)]
              congr 1; ring
        _ = ENNReal.ofReal B := by
          rw [← ofReal_integral_eq_lintegral_ofReal
            (integrableOn_exp_mul_Ioi (div_neg_of_neg_of_pos (by norm_num) hB) 0)
            (by filter_upwards with t; exact (exp_pos _).le)]
          congr 1
          rw [integral_exp_mul_Ioi (div_neg_of_neg_of_pos (by norm_num) hB)]
          simp [mul_zero, exp_zero]
    calc ∫ ω, (X ω - A) ∂μ
      ≤ ∫ ω, max (X ω - A) 0 ∂μ := by
        exact integral_mono_ae hIntXA hIntMax
          (by filter_upwards with ω; exact le_max_left _ _)
      _ = (∫⁻ ω, ENNReal.ofReal (max (X ω - A) 0) ∂μ).toReal := by
        exact integral_eq_lintegral_of_nonneg_ae
          (by filter_upwards with ω; exact le_max_right _ _) hMeasMax
      _ ≤ B := by
        rw [← ENNReal.toReal_ofReal hB.le]
        exact ENNReal.toReal_mono (ENNReal.ofReal_ne_top) hlint
  · rw [integral_undef hInt]; linarith
/-- Uniform-in-`δ` form of the high-probability bound from Theorem 3.15: there is a
single constant `C` such that for every `δ ∈ (0,1]`, the high-probability bound holds. -/

end Chapter3


-- created on 2026-10-23
