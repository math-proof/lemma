import Mathlib
import sympy.Basic
import Def.v1.Atlas.HighDimensionalStatistics.code.Chapter3.Cor_3_16
open Real MeasureTheory Chapter3


namespace Chapter3

/--
[IsBICEstimatorTrig_to_matrix_optimality](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter3/Cor_3_16.lean)
-/
@[path]
lemma IsBICEstimatorTrig_to_matrix_optimality
  {n : ℕ}
  {Y : Ω → Fin n → ℝ}
  {θhat : Ω → Fin (n - 1) → ℝ}
  {τsq : ℝ}
-- given
  (hn : 0 < n)
  (hBIC : IsBICEstimatorTrig Y θhat τsq) :
-- imply
  let Φ := trigDesignMatrix n (n - 1) ∀ ω θ, (1 / (n : ℝ)) * ∑ i : Fin n, (Y ω i - (Φ.mulVec (θhat ω)) i) ^ 2 + τsq * ↑((Finset.univ.filter (fun j => θhat ω j ≠ 0)).card) ≤ (1 / (n : ℝ)) * ∑ i : Fin n, (Y ω i - (Φ.mulVec θ) i) ^ 2 + τsq * ↑((Finset.univ.filter (fun j => θ j ≠ 0)).card) := by
-- proof
  intro Φ ω θ
  have h := hBIC ω θ
  have h_eq_hat : ∀ i : Fin n,
    trigLinComb (n - 1) (θhat ω) ((i : ℝ) / (n : ℝ)) =
    (trigDesignMatrix n (n - 1)).mulVec (θhat ω) i :=
    fun i => trigLinComb_eq_mulVec n (n - 1) hn (θhat ω) i
  have h_eq_θ : ∀ i : Fin n,
    trigLinComb (n - 1) θ ((i : ℝ) / (n : ℝ)) =
    (trigDesignMatrix n (n - 1)).mulVec θ i :=
    fun i => trigLinComb_eq_mulVec n (n - 1) hn θ i
  simp_rw [h_eq_hat, h_eq_θ] at h
  exact h

end Chapter3

namespace Chapter3

/--
[IsLassoEstimatorTrig_to_matrix_optimality](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter3/Cor_3_16.lean)
-/
@[path]
lemma IsLassoEstimatorTrig_to_matrix_optimality
  {n : ℕ}
  {Y : Ω → Fin n → ℝ}
  {θhat : Ω → Fin (n - 1) → ℝ}
  {τ : ℝ}
-- given
  (hn : 0 < n)
  (hLasso : IsLassoEstimatorTrig Y θhat τ) :
-- imply
  let Φ := trigDesignMatrix n (n - 1) ∀ ω θ, (1 / (n : ℝ)) * ∑ i : Fin n, (Y ω i - (Φ.mulVec (θhat ω)) i) ^ 2 + 2 * τ * ∑ j : Fin (n - 1), := by
-- proof
  intro Φ ω θ
  have h := hLasso ω θ
  have h_eq_hat : ∀ i : Fin n,
    trigLinComb (n - 1) (θhat ω) ((i : ℝ) / (n : ℝ)) =
    (trigDesignMatrix n (n - 1)).mulVec (θhat ω) i :=
    fun i => trigLinComb_eq_mulVec n (n - 1) hn (θhat ω) i
  have h_eq_θ : ∀ i : Fin n,
    trigLinComb (n - 1) θ ((i : ℝ) / (n : ℝ)) =
    (trigDesignMatrix n (n - 1)).mulVec θ i :=
    fun i => trigLinComb_eq_mulVec n (n - 1) hn θ i
  simp_rw [h_eq_hat, h_eq_θ] at h
  exact h

end Chapter3

namespace Chapter3

/--
[integral_split_sq_sub](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter3/Cor_3_16.lean)
-/
@[path]
lemma integral_split_sq_sub
  {a : ℝ → ℝ}
  {b : ℝ → ℝ}
-- given
  (ha : Integrable (fun x => a x ^ 2) (volume.restrict (Set.Icc 0 1)))
  (hb : Integrable (fun x => b x ^ 2) (volume.restrict (Set.Icc 0 1)))
  (hab : Integrable (fun x => a x * b x) (volume.restrict (Set.Icc 0 1))) :
-- imply
  ∫ x in Set.Icc (0 : ℝ) 1, (a x ^ 2 - 2 * a x * b x + b x ^ 2) = (∫ x in Set.Icc (0 : ℝ) 1, a x ^ 2) + (∫ x in Set.Icc (0 : ℝ) 1, b x ^ 2) - 2 * (∫ x in Set.Icc (0 : ℝ) 1, a x * b x) := by
-- proof
  have hab2 : Integrable (fun x => (-2) * (a x * b x)) (volume.restrict (Set.Icc 0 1)) :=
    hab.const_mul (-2)
  have hab' : Integrable (fun x => a x ^ 2 + b x ^ 2) (volume.restrict (Set.Icc 0 1)) :=
    ha.add hb
  have heq : ∀ x, a x ^ 2 - 2 * a x * b x + b x ^ 2 =
    (a x ^ 2 + b x ^ 2) + (-2) * (a x * b x) := by intro x; ring
  simp_rw [heq]
  rw [integral_add hab' hab2]
  rw [integral_add ha hb]
  rw [integral_const_mul]
  ring

end Chapter3

namespace Chapter3

/--
[trigLinComb_continuous](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter3/Cor_3_16.lean)
-/
@[path]
lemma trigLinComb_continuous
  {N : ℕ}
  {θ : Fin N → ℝ} :
-- imply
  Continuous (fun x => trigLinComb N θ x) := by
-- proof
  unfold trigLinComb
  apply continuous_finset_sum
  intro j _
  exact continuous_const.mul (trigBasis_continuous (j.val + 1))

end Chapter3

namespace Chapter3

/--
[integrableOn_sq_trigLinComb_sub_f](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter3/Cor_3_16.lean)
-/
@[path]
lemma integrableOn_sq_trigLinComb_sub_f
  {N : ℕ}
  {f : ℝ → ℝ}
  {θ : Fin N → ℝ}
-- given
  (_hθ : ∀ j : Fin N, θ j = fourierCoeff f (j.val + 1))
  (hf_cont : Continuous f) :
-- imply
  Integrable (fun x => (trigLinComb N θ x - f x) ^ 2) (volume.restrict (Set.Icc 0 1)) := by
-- proof
  apply ContinuousOn.integrableOn_compact isCompact_Icc
  exact (((trigLinComb_continuous N θ).sub hf_cont).pow 2).continuousOn

end Chapter3

namespace Chapter3

/--
[integrableOn_trigLinComb_sub_f_mul_trigLinComb](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter3/Cor_3_16.lean)
-/
@[path]
lemma integrableOn_trigLinComb_sub_f_mul_trigLinComb
  {N : ℕ}
  {f : ℝ → ℝ}
  {θ_full θ_tail : Fin N → ℝ}
-- given
  (_hθ : ∀ j : Fin N, θ_full j = fourierCoeff f (j.val + 1))
  (hf_cont : Continuous f) :
-- imply
  Integrable (fun x => (trigLinComb N θ_full x - f x) * trigLinComb N θ_tail x) (volume.restrict (Set.Icc 0 1)) := by
-- proof
  apply ContinuousOn.integrableOn_compact isCompact_Icc
  exact (((trigLinComb_continuous N θ_full).sub hf_cont).mul
    (trigLinComb_continuous N θ_tail)).continuousOn

end Chapter3

namespace Chapter3

/--
[L2_cross_term_orthogonal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter3/Cor_3_16.lean)
-/
@[path]
lemma L2_cross_term_orthogonal
  {N : ℕ}
  {f : ℝ → ℝ}
  {θ_full : Fin N → ℝ}
  {θ_tail : Fin N → ℝ}
-- given
  (hθ : ∀ j : Fin N, θ_full j = fourierCoeff f (j.val + 1))
  (hf_cont : Continuous f) :
-- imply
  ∫ x in Set.Icc (0 : ℝ) 1, (trigLinComb N θ_full x - f x) * trigLinComb N θ_tail x = 0 := by
-- proof
  simp only [trigLinComb]
  have h_inner_zero : ∀ j' : Fin N,
    ∫ x in Set.Icc (0 : ℝ) 1,
      ((∑ j : Fin N, θ_full j * trigBasis (↑j + 1) x) - f x) *
      trigBasis (↑j' + 1) x = 0 := by
    intro j'
    have hj'_pos : 0 < (↑j' : ℕ) + 1 := Nat.succ_pos _
    have hA : ∫ x in Set.Icc (0 : ℝ) 1,
      (∑ j : Fin N, θ_full j * trigBasis (↑j + 1) x) * trigBasis (↑j' + 1) x =
      θ_full j' := by
      simp_rw [Finset.sum_mul]
      rw [integral_finset_sum Finset.univ (fun j _ => by
        apply ContinuousOn.integrableOn_compact isCompact_Icc
        apply ContinuousOn.mul
        · exact (continuous_const.mul (trigBasis_continuous _)).continuousOn
        · exact (trigBasis_continuous _).continuousOn)]
      simp_rw [mul_assoc, integral_const_mul]
      simp_rw [trigBasis_L2_orthonormal _ _ (Nat.succ_pos _) hj'_pos]
      simp only [mul_ite, mul_one, mul_zero]
      simp only [Nat.succ_eq_add_one, Nat.add_right_cancel_iff, Fin.val_inj]
      rw [Finset.sum_ite_eq' Finset.univ j' (fun j => θ_full j)]
      simp [Finset.mem_univ]
    have hB : ∫ x in Set.Icc (0 : ℝ) 1, f x * trigBasis (↑j' + 1) x =
      θ_full j' := by
      rw [hθ j']
      rfl
    have h_eq : ∀ x, ((∑ j : Fin N, θ_full j * trigBasis (↑j + 1) x) - f x) *
      trigBasis (↑j' + 1) x =
      (∑ j : Fin N, θ_full j * trigBasis (↑j + 1) x) * trigBasis (↑j' + 1) x -
      f x * trigBasis (↑j' + 1) x := by
      intro x; ring
    simp_rw [h_eq]
    rw [integral_sub
      (by apply ContinuousOn.integrableOn_compact isCompact_Icc
        apply ContinuousOn.mul
        · apply continuousOn_finset_sum; intro j _
          exact (continuous_const.mul (trigBasis_continuous _)).continuousOn
        · exact (trigBasis_continuous _).continuousOn)
      (by apply ContinuousOn.integrableOn_compact isCompact_Icc
        exact (hf_cont.mul (trigBasis_continuous _)).continuousOn)]
    linarith [hA, hB]
  have h_prod_sum : ∀ x : ℝ,
    (∑ j : Fin N, θ_full j * trigBasis (↑j + 1) x - f x) *
    (∑ j : Fin N, θ_tail j * trigBasis (↑j + 1) x) =
    ∑ j' : Fin N, θ_tail j' *
      ((∑ j : Fin N, θ_full j * trigBasis (↑j + 1) x - f x) * trigBasis (↑j' + 1) x) := by
    intro x
    simp_rw [Finset.mul_sum, mul_comm (θ_tail _) _, ← mul_assoc]
  simp_rw [h_prod_sum]
  rw [integral_finset_sum Finset.univ (fun j' _ => by
    apply ContinuousOn.integrableOn_compact isCompact_Icc
    apply ContinuousOn.mul
    · exact continuousOn_const
    · apply ContinuousOn.mul
      · apply ContinuousOn.sub
        · apply continuousOn_finset_sum; intro j _
          exact (continuous_const.mul (trigBasis_continuous _)).continuousOn
        · exact hf_cont.continuousOn
      · exact (trigBasis_continuous _).continuousOn)]
  simp_rw [integral_const_mul, h_inner_zero, mul_zero, Finset.sum_const_zero]

end Chapter3

namespace Chapter3

/--
[L2normSq_truncation_Pythagorean](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter3/Cor_3_16.lean)
-/
@[path]
lemma L2normSq_truncation_Pythagorean
  {n : ℕ}
  {f : ℝ → ℝ}
  {θstar : ℕ → ℝ}
  {M : ℕ}
-- given
  (_hθstar : ∀ j, θstar j = fourierCoeff f j)
  (_hM_le : M ≤ n - 1)
  (hf_cont : Continuous f) :
-- imply
  L2normSq (fun x => trigLinComb (n - 1) (fun j : Fin (n - 1) => if (j : ℕ) < M then θstar (j.val + 1) else 0) x - f x) = (((Finset.univ : Finset (Fin (n - 1))).filter (fun j : Fin (n - 1) => ¬ (j : ℕ) < M)).sum (fun j : Fin (n - 1) => (θstar (j.val + 1)) ^ 2)) + L2normSq (fun x => trigLinComb (n - 1) (fun j : Fin (n - 1) => θstar (j.val + 1)) x - f x) := by
-- proof
  set N := n - 1
  set θ_full : Fin N → ℝ := fun j => θstar (j.val + 1)
  set θ_tail : Fin N → ℝ := fun j => if (j : ℕ) < M then 0 else θstar (j.val + 1)
  set θ_trunc : Fin N → ℝ := fun j => if (j : ℕ) < M then θstar (j.val + 1) else 0
  have h_split : ∀ j : Fin N, θ_trunc j = θ_full j - θ_tail j := by
    intro j; simp only [θ_trunc, θ_full, θ_tail]; split_ifs <;> ring
  have h_fn : ∀ x, trigLinComb N θ_trunc x - f x =
    (trigLinComb N θ_full x - f x) - trigLinComb N θ_tail x := by
    intro x; simp only [trigLinComb]
    have : ∑ j : Fin N, θ_trunc j * trigBasis (j.val + 1) x =
      (∑ j : Fin N, θ_full j * trigBasis (j.val + 1) x) -
      ∑ j : Fin N, θ_tail j * trigBasis (j.val + 1) x := by
      rw [← Finset.sum_sub_distrib]
      congr 1; ext j; rw [h_split]; ring
    linarith [this]
  conv_lhs => rw [show (fun x => trigLinComb N θ_trunc x - f x) =
    (fun x => (trigLinComb N θ_full x - f x) - trigLinComb N θ_tail x) from funext h_fn]
  unfold L2normSq
  have h_expand : ∀ x, ((trigLinComb N θ_full x - f x) - trigLinComb N θ_tail x) ^ 2 =
    (trigLinComb N θ_full x - f x) ^ 2 - 2 * (trigLinComb N θ_full x - f x) * trigLinComb N θ_tail x +
    (trigLinComb N θ_tail x) ^ 2 := by
    intro x; ring
  simp_rw [h_expand]
  have hθ_fourier : ∀ j : Fin N, θ_full j = fourierCoeff f (j.val + 1) := by
    intro j; simp [θ_full]; exact _hθstar (j.val + 1)
  have h_int_sq_sub : Integrable (fun x => (trigLinComb N θ_full x - f x) ^ 2)
    (volume.restrict (Set.Icc 0 1)) :=
    integrableOn_sq_trigLinComb_sub_f f θ_full hθ_fourier hf_cont
  have h_int_sq_tail : Integrable (fun x => (trigLinComb N θ_tail x) ^ 2)
    (volume.restrict (Set.Icc 0 1)) := by
    apply ContinuousOn.integrableOn_compact isCompact_Icc
    exact (Continuous.pow (trigLinComb_continuous N θ_tail) 2).continuousOn
  have h_int_cross : Integrable (fun x => (trigLinComb N θ_full x - f x) * trigLinComb N θ_tail x)
    (volume.restrict (Set.Icc 0 1)) :=
    integrableOn_trigLinComb_sub_f_mul_trigLinComb f θ_full θ_tail hθ_fourier hf_cont
  rw [show ∫ x in Set.Icc (0 : ℝ) 1,
    (trigLinComb N θ_full x - f x) ^ 2 -
    2 * (trigLinComb N θ_full x - f x) * trigLinComb N θ_tail x +
    (trigLinComb N θ_tail x) ^ 2 =
    (∫ x in Set.Icc (0 : ℝ) 1, (trigLinComb N θ_full x - f x) ^ 2) +
    (∫ x in Set.Icc (0 : ℝ) 1, (trigLinComb N θ_tail x) ^ 2) -
    2 * (∫ x in Set.Icc (0 : ℝ) 1, (trigLinComb N θ_full x - f x) * trigLinComb N θ_tail x)
    from integral_split_sq_sub _ _ h_int_sq_sub h_int_sq_tail h_int_cross]
  have h_cross : ∫ x in Set.Icc (0 : ℝ) 1,
    (trigLinComb N θ_full x - f x) * trigLinComb N θ_tail x = 0 :=
    L2_cross_term_orthogonal f θ_full θ_tail hθ_fourier hf_cont
  rw [h_cross, mul_zero, sub_zero]
  have h_tail_sq : ∫ x in Set.Icc (0 : ℝ) 1, (trigLinComb N θ_tail x) ^ 2 =
    (Finset.univ.filter (fun j : Fin N => ¬(j : ℕ) < M)).sum
      (fun j : Fin N => (θstar (j.val + 1)) ^ 2) := by
    have := L2_norm_eq_sum_sq N θ_tail
    unfold L2normSq at this
    rw [show (fun x => ∑ j : Fin N, θ_tail j * trigBasis (↑j + 1) x) =
      (fun x => trigLinComb N θ_tail x) from by ext x; simp [trigLinComb]] at this
    rw [this]
    conv_lhs => rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun j : Fin N => (j : ℕ) < M)]
    simp only [not_lt]
    have h_zero : (Finset.univ.filter (fun j : Fin N => (j : ℕ) < M)).sum
      (fun j => θ_tail j ^ 2) = 0 := by
      apply Finset.sum_eq_zero; intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      simp [θ_tail, if_pos hj]
    rw [h_zero, zero_add]
    apply Finset.sum_congr
    · ext j; simp
    · intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      simp [θ_tail, if_neg (not_lt.mpr hj)]
  rw [h_tail_sq]; ring

end Chapter3

namespace Chapter3

/--
[aliasing_tail_L2_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter3/Cor_3_16.lean)
-/
@[path]
lemma aliasing_tail_L2_bound
  {β : ℝ}
  {Q : ℝ}
  {θstar : ℕ → ℝ}
  {n : ℕ}
-- given
  (hβ_pos : 0 < β)
  (hQ : 0 < Q)
  (hSobolev : ∀ (K : ℕ), ∑ j : Fin K, (sobolevCoeff β (j.val + 1)) ^ 2 * (θstar j.val) ^ 2 ≤ Q)
  (hn : 2 ≤ n) :
-- imply
  ∀ (K : ℕ), ∑ j ∈ Finset.Ico (n - 1) K, (θstar j) ^ 2 ≤ Q * ((n - 1 : ℕ) : ℝ) ^ (-(2 * β)) := by
-- proof
  intro K
  by_cases hK : n - 1 ≤ K
  ·
    have hM_pos : 0 < (n - 1 : ℕ) := by omega
    have hM_real_pos : (0 : ℝ) < ((n - 1 : ℕ) : ℝ) := Nat.cast_pos.mpr hM_pos
    have hterm : ∀ j ∈ Finset.Ico (n - 1) K,
      (θstar ↑j) ^ 2 ≤ ((n - 1 : ℕ) : ℝ) ^ (-(2 * β)) *
        ((sobolevCoeff β (↑j + 1)) ^ 2 * (θstar ↑j) ^ 2) := by
      intro j hj
      simp only [Finset.mem_Ico] at hj
      have hMj : (n - 1 : ℕ) ≤ j := hj.1
      have hw := sobolev_weight_ge_rpow β hβ_pos (n - 1) j hMj
      by_cases hθ : θstar j = 0
      · simp [hθ]
      · have hMpow_pos : 0 < ((n - 1 : ℕ) : ℝ) ^ (2 * β) := rpow_pos_of_pos hM_real_pos _
        rw [rpow_neg hM_real_pos.le, ← div_eq_inv_mul]
        rw [le_div_iff₀ hMpow_pos]
        nlinarith [sq_nonneg (θstar j)]
    calc ∑ j ∈ Finset.Ico (n - 1) K, (θstar j) ^ 2
      ≤ ∑ j ∈ Finset.Ico (n - 1) K, ((n - 1 : ℕ) : ℝ) ^ (-(2 * β)) *
        ((sobolevCoeff β (↑j + 1)) ^ 2 * (θstar j) ^ 2) :=
        Finset.sum_le_sum hterm
      _ = ((n - 1 : ℕ) : ℝ) ^ (-(2 * β)) *
        ∑ j ∈ Finset.Ico (n - 1) K, (sobolevCoeff β (↑j + 1)) ^ 2 * (θstar j) ^ 2 := by
        rw [← Finset.mul_sum]
      _ ≤ ((n - 1 : ℕ) : ℝ) ^ (-(2 * β)) * Q := by
        gcongr
        have hSobK := hSobolev K
        calc ∑ j ∈ Finset.Ico (n - 1) K,
          (sobolevCoeff β (↑j + 1)) ^ 2 * (θstar j) ^ 2
          ≤ ∑ j ∈ Finset.range K,
            (sobolevCoeff β (↑j + 1)) ^ 2 * (θstar j) ^ 2 := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro x hx
              simp only [Finset.mem_Ico] at hx
              simp only [Finset.mem_range]
              exact hx.2
            · intros i _ _; exact mul_nonneg (sq_nonneg _) (sq_nonneg _)
          _ = ∑ j : Fin K, (sobolevCoeff β (↑j.val + 1)) ^ 2 * (θstar j.val) ^ 2 := by
            simp only [← Fin.sum_univ_eq_sum_range]
          _ ≤ Q := hSobK
      _ = Q * ((n - 1 : ℕ) : ℝ) ^ (-(2 * β)) := by ring
  ·
    push Not at hK
    have : Finset.Ico (n - 1) K = ∅ := Finset.Ico_eq_empty (by omega)
    simp [this]
    apply mul_nonneg
    · linarith
    · apply rpow_nonneg
      exact Nat.cast_nonneg _

end Chapter3

namespace Chapter3

/--
[coeff_tail_sq_sum_le_rpow](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter3/Cor_3_16.lean)
-/
@[path]
lemma coeff_tail_sq_sum_le_rpow
  {β : ℝ}
  {Q : ℝ}
  {θstar : ℕ → ℝ}
  {n : ℕ}
  {M : ℕ}
-- given
  (hβ_pos : 0 < β)
  (_hQ : 0 < Q)
  (hSobolev : ∀ (K : ℕ), ∑ j : Fin K, (sobolevCoeff β (j.val + 1)) ^ 2 * (θstar j.val) ^ 2 ≤ Q)
  (_hn : 2 ≤ n)
  (hM_pos : 0 < M)
  (_hM_le : M ≤ n - 1) :
-- imply
  (((Finset.univ : Finset (Fin (n - 1))).filter (fun j : Fin (n - 1) => ¬ (j : ℕ) < M)).sum (fun j : Fin (n - 1) => (θstar (j.val + 1)) ^ 2)) ≤ Q * (M : ℝ) ^ (-(2 * β)) := by
-- proof
  have hM_real_pos : (0 : ℝ) < (M : ℝ) := Nat.cast_pos.mpr hM_pos
  have hterm : ∀ j : Fin (n - 1), ¬(j : ℕ) < M →
    (θstar (j.val + 1)) ^ 2 ≤
    (M : ℝ) ^ (-(2 * β)) * ((sobolevCoeff β (j.val + 2)) ^ 2 * (θstar (j.val + 1)) ^ 2) := by
    intro j hj
    push Not at hj
    have hw := sobolev_weight_ge_rpow β hβ_pos M (j.val + 1) (by omega)
    by_cases hθ : θstar (j.val + 1) = 0
    · simp [hθ]
    · have hMpow_pos : 0 < (M : ℝ) ^ (2 * β) := rpow_pos_of_pos hM_real_pos _
      rw [rpow_neg hM_real_pos.le, ← div_eq_inv_mul]
      rw [le_div_iff₀ hMpow_pos]
      nlinarith [sq_nonneg (θstar (j.val + 1))]
  have hShiftedSum : ((Finset.univ : Finset (Fin (n - 1))).sum
    (fun j : Fin (n - 1) => (sobolevCoeff β (j.val + 2)) ^ 2 * (θstar (j.val + 1)) ^ 2)) ≤ Q := by
    let g := fun k : ℕ => (sobolevCoeff β (k + 1)) ^ 2 * (θstar k) ^ 2
    have hg_nn : ∀ k, 0 ≤ g k := fun k => mul_nonneg (sq_nonneg _) (sq_nonneg _)
    show (Finset.univ : Finset (Fin (n - 1))).sum
      (fun j : Fin (n - 1) => g (j.val + 1)) ≤ Q
    have hSobN : (Finset.univ : Finset (Fin n)).sum (fun j : Fin n => g j.val) ≤ Q :=
      hSobolev n
    rw [Fin.sum_univ_eq_sum_range] at hSobN
    have hconv : (Finset.univ : Finset (Fin (n - 1))).sum (fun j => g (↑j + 1)) =
      ∑ i ∈ Finset.range (n - 1), g (i + 1) := by
      rw [← Fin.sum_univ_eq_sum_range (fun i => g (i + 1))]
    rw [hconv]
    have hn_eq : n = (n - 1) + 1 := by omega
    rw [hn_eq] at hSobN
    rw [Finset.sum_range_succ'] at hSobN
    linarith [hg_nn 0]
  calc (((Finset.univ : Finset (Fin (n - 1))).filter
    (fun j : Fin (n - 1) => ¬(j : ℕ) < M)).sum
    (fun j : Fin (n - 1) => (θstar (j.val + 1)) ^ 2))
    ≤ (((Finset.univ : Finset (Fin (n - 1))).filter
      (fun j : Fin (n - 1) => ¬(j : ℕ) < M)).sum
      (fun j : Fin (n - 1) => (M : ℝ) ^ (-(2 * β)) *
        ((sobolevCoeff β (j.val + 2)) ^ 2 * (θstar (j.val + 1)) ^ 2))) := by
      apply Finset.sum_le_sum
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      exact hterm j hj
    _ = (M : ℝ) ^ (-(2 * β)) *
      (((Finset.univ : Finset (Fin (n - 1))).filter
        (fun j : Fin (n - 1) => ¬(j : ℕ) < M)).sum
        (fun j : Fin (n - 1) => (sobolevCoeff β (j.val + 2)) ^ 2 * (θstar (j.val + 1)) ^ 2)) := by
      rw [← Finset.mul_sum]
    _ ≤ (M : ℝ) ^ (-(2 * β)) * Q := by
      gcongr
      calc (((Finset.univ : Finset (Fin (n - 1))).filter
        (fun j : Fin (n - 1) => ¬(j : ℕ) < M)).sum
        (fun j : Fin (n - 1) => (sobolevCoeff β (j.val + 2)) ^ 2 * (θstar (j.val + 1)) ^ 2))
        ≤ ((Finset.univ : Finset (Fin (n - 1))).sum
          (fun j : Fin (n - 1) => (sobolevCoeff β (j.val + 2)) ^ 2 * (θstar (j.val + 1)) ^ 2)) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · exact Finset.filter_subset _ _
          · intros i _ _
            exact mul_nonneg (sq_nonneg _) (sq_nonneg _)
        _ ≤ Q := hShiftedSum
    _ = Q * (M : ℝ) ^ (-(2 * β)) := by ring

end Chapter3

namespace Chapter3

/--
[trigLinComb_eq_mulVec_apply](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter3/Cor_3_16.lean)
-/
@[path]
lemma trigLinComb_eq_mulVec_apply
  {n M : ℕ}
  {θ : Fin M → ℝ}
  {i : Fin n}
-- given
  (hn : 0 < n) :
-- imply
  trigLinComb M θ ((i : ℝ) / (n : ℝ)) = (trigDesignMatrix n M).mulVec θ i := by
-- proof
  simp only [trigLinComb, Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro j _
  rw [trigDesignMatrix_eq_trigBasis n M hn i j]
  ring

end Chapter3

namespace Chapter3

/--
[empiricalNormSq_eq_MSE_trigDesign](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter3/Cor_3_16.lean)
-/
@[path]
lemma empiricalNormSq_eq_MSE_trigDesign
  {n : ℕ}
  {M : ℕ}
  {θ : Fin M → ℝ}
  {f : ℝ → ℝ}
-- given
  (hn : 0 < n) :
-- imply
  empiricalNormSq n (fun x => trigLinComb M θ x - f x) = Rigollet.Chapter3.MSE_35 ((trigDesignMatrix n M).mulVec θ) (fun i => f ((i : ℝ) / (n : ℝ))) := by
-- proof
  simp only [empiricalNormSq, Rigollet.Chapter3.MSE_35]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  rw [trigLinComb_eq_mulVec_apply n M hn θ i]

end Chapter3

namespace Chapter3

/--
[trig_design_colnorm_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter3/Cor_3_16.lean)
-/
@[path]
lemma trig_design_colnorm_bound
  {n : ℕ}
-- given
  (hn : 2 ≤ n) :
-- imply
  ∀ j : Fin (n - 1), ∑ i : Fin n, (trigDesignMatrix n (n - 1) i j) ^ 2 ≤ ↑n := by
-- proof
  intro j
  have h313 := lemma_3_13 n (n - 1) (by omega) (le_refl _)
  have h := congr_fun (congr_fun h313 j) j
  simp only [Matrix.mul_apply, Matrix.transpose_apply] at h
  simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_one,
    ↓reduceIte] at h
  have key : ∀ i : Fin n, (trigDesignMatrix n (n - 1) i j) ^ 2 =
    trigDesignMatrix n (n - 1) i j * trigDesignMatrix n (n - 1) i j := by
    intro i; ring
  simp_rw [key]
  linarith

end Chapter3

namespace Chapter3

/--
[subGaussianNoiseVec_to_subGaussianNoise](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter3/Cor_3_16.lean)
-/
@[path]
lemma subGaussianNoiseVec_to_subGaussianNoise
  [MeasurableSpace Ω]
  {n : ℕ}
  {ε : Ω → Fin n → ℝ}
  {σ : ℝ}
  {μ : MeasureTheory.Measure Ω}
-- given
  (h : IsSubGaussianNoiseVec ε (σ ^ 2) μ) :
-- imply
  Rigollet.Chapter3.IsSubGaussianNoise ε σ μ :=
-- proof
  h.bound

end Chapter3

namespace Chapter3

/--
[subGaussianNoiseVec_to_IsSubGaussian](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter3/Cor_3_16.lean)
-/
@[path]
lemma subGaussianNoiseVec_to_IsSubGaussian
  [MeasurableSpace Ω]
  {n : ℕ}
  {μ : MeasureTheory.Measure Ω}
  [MeasureTheory.IsProbabilityMeasure μ]
  {ε : Ω → Fin n → ℝ}
  {σ : ℝ}
-- given
  (hσ : 0 < σ)
  (hsubG : IsSubGaussianNoiseVec ε (σ ^ 2) μ)
  (hMeasε : ∀ i, Measurable (fun ω => ε ω i))
  (hZeroMean : ∀ i, ∫ ω, ε ω i ∂μ = 0) :
-- imply
  ∀ i : Fin n, IsSubGaussian (fun ω => ε ω i) (σ ^ 2) μ := by
-- proof
  intro i
  exact ⟨hsubG.integ i, hZeroMean i, hsubG.exp_integ i, hsubG.bound i⟩

end Chapter3

namespace Chapter3

/--
[ORT_empirical_eq_L2](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter3/Cor_3_16.lean)
-/
@[path]
lemma ORT_empirical_eq_L2
  {n : ℕ}
  {M : ℕ}
  {θ : Fin M → ℝ}
-- given
  (hn : 2 ≤ n)
  (hM : M ≤ n - 1) :
-- imply
  empiricalNormSq n (fun x => trigLinComb M θ x) = L2normSq (fun x => trigLinComb M θ x) := by
-- proof
  have hn_pos : 0 < n := by omega
  have hORT := ORT_L2_eq_empirical_normSq n M hn_pos hM θ
  unfold empiricalNormSq trigLinComb
  rw [← hORT]

end Chapter3

namespace Chapter3

/--
[tail_integration_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter3/Cor_3_16.lean)
-/
@[path]
lemma tail_integration_bound
  [MeasurableSpace Ω]
  {μ : Measure Ω}
  [IsProbabilityMeasure μ]
  {X : Ω → ℝ}
  {A : ℝ}
  {B : ℝ}
-- given
  (hMeas : Measurable X)
  (hA_pos : 0 < A)
  (hB_pos : 0 < B)
  (hTail : ∀ (δ : ℝ), 0 < δ → δ ≤ 1 → μ {ω | X ω ≤ A + B * Real.log (1 / δ)} ≥ ENNReal.ofReal (1 - δ)) :
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
      ((hMeas.sub measurable_const).max measurable_const).aestronglyMeasurable
    have hlint : ∫⁻ ω, ENNReal.ofReal (max (X ω - A) 0) ∂μ ≤ ENNReal.ofReal B := by
      rw [lintegral_eq_lintegral_meas_lt μ
        (by filter_upwards with ω; exact le_max_right _ _)
        ((hMeas.sub measurable_const).max measurable_const).aemeasurable]
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
              (div_nonpos_of_nonpos_of_nonneg (by norm_num) hB_pos.le) ht.le)
          have hTail' := hTail δ hδ_pos hδ_le
          have key : A + B * Real.log (1 / δ) = A + t := by
            congr 1; rw [one_div, Real.log_inv, Real.log_exp]; field_simp
          rw [key] at hTail'
          have hms : MeasurableSet {ω | X ω ≤ A + t} := hMeas measurableSet_Iic
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
            (integrableOn_exp_mul_Ioi (div_neg_of_neg_of_pos (by norm_num) hB_pos) 0)
            (by filter_upwards with t; exact (exp_pos _).le)]
          congr 1
          rw [integral_exp_mul_Ioi (div_neg_of_neg_of_pos (by norm_num) hB_pos)]
          simp [mul_zero, exp_zero]
    calc ∫ ω, (X ω - A) ∂μ
      ≤ ∫ ω, max (X ω - A) 0 ∂μ := by
        exact integral_mono_ae hIntXA hIntMax
          (by filter_upwards with ω; exact le_max_left _ _)
      _ = (∫⁻ ω, ENNReal.ofReal (max (X ω - A) 0) ∂μ).toReal := by
        exact integral_eq_lintegral_of_nonneg_ae
          (by filter_upwards with ω; exact le_max_right _ _) hMeasMax
      _ ≤ B := by
        rw [← ENNReal.toReal_ofReal hB_pos.le]
        exact ENNReal.toReal_mono (ENNReal.ofReal_ne_top) hlint
  · rw [integral_undef hInt]; linarith

end Chapter3

namespace Chapter3

/--
[cor_3_16_rate_computation](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter3/Cor_3_16.lean)
-/
@[path]
lemma cor_3_16_rate_computation
  {n : ℕ}
  {β : ℝ}
  {M : ℕ}
  {σ : ℝ}
-- given
  (hn : 2 ≤ n)
  (_hβ_pos : 0 < β)
  (_hβ_lower : β ≥ (1 + Real.sqrt 5) / 4)
  (hM_pos : 0 < M)
  (_hM_le : M ≤ n - 1)
  (_hσ : 0 < σ) :
-- imply
  ∃ (C' : ℝ), 0 < C' ∧ ∀ (δ : ℝ), 0 < δ → δ ≤ 1 → (M : ℝ) ^ (-(2 * β)) + ((n - 1 : ℕ) : ℝ) ^ (-(2 * β)) + (M : ℝ) * Real.log ((n : ℝ) * Real.exp 1) / (n : ℝ) + σ ^ 2 * Real.log (1 / δ) / (n : ℝ) ≤ C' * (n : ℝ) ^ (-(2 * β) / (2 * β + 1)) + C' * σ ^ 2 * Real.log (1 / δ) / (n : ℝ) := by
-- proof
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have hM_real_pos : (0 : ℝ) < (M : ℝ) := Nat.cast_pos.mpr hM_pos
  have hn1_real_pos : (0 : ℝ) < ((n - 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega)
  set r := (n : ℝ) ^ (-(2 * β) / (2 * β + 1))
  have hr_pos : 0 < r := rpow_pos_of_pos hn_pos _
  set A := (M : ℝ) ^ (-(2 * β)) + ((n - 1 : ℕ) : ℝ) ^ (-(2 * β)) +
    (M : ℝ) * Real.log ((n : ℝ) * Real.exp 1) / (n : ℝ)
  have hA_pos : 0 < A := by
    apply add_pos (add_pos _ _) _
    · exact rpow_pos_of_pos hM_real_pos _
    · exact rpow_pos_of_pos hn1_real_pos _
    · apply div_pos (mul_pos hM_real_pos _) hn_pos
      apply Real.log_pos
      have hn1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
      linarith [mul_lt_mul_of_pos_left (one_lt_exp_iff.mpr one_pos) hn_pos]
  refine ⟨A / r + 1, by linarith [div_pos hA_pos hr_pos], ?_⟩
  intro δ hδ_pos hδ_le
  set L := σ ^ 2 * Real.log (1 / δ)
  have hL_nonneg : 0 ≤ L := by
    apply mul_nonneg (sq_nonneg σ)
    apply Real.log_nonneg
    rw [le_div_iff₀ hδ_pos]; linarith
  suffices h : A + L / ↑n ≤ (A / r + 1) * r + (A / r + 1) * L / ↑n by
    convert h using 1; ring
  have h_expand_r : (A / r + 1) * r = A + r := by
    rw [add_mul, div_mul_cancel₀ A (ne_of_gt hr_pos), one_mul]
  have hAr_nonneg : 0 ≤ A / r := div_nonneg hA_pos.le hr_pos.le
  have h_expand_L : (A / r + 1) * L / ↑n ≥ L / ↑n := by
    apply div_le_div_of_nonneg_right _ hn_pos.le
    calc L = 1 * L := (one_mul L).symm
      _ ≤ (A / r + 1) * L := by
        apply mul_le_mul_of_nonneg_right _ hL_nonneg
        linarith
  linarith
/-- Expectation version of Corollary 3.16, derived from the tail bound:
`E ‖φ_{θ̂} - f‖²_{L²} ≲ σ² (log n / n)^{2β/(2β+1)}`. -/

end Chapter3


-- created on 2026-10-23
