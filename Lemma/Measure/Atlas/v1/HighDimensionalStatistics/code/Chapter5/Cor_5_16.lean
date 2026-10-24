import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.HighDimensionalStatistics.code.Chapter5.Cor_5_16
open Real MeasureTheory InformationTheory MinimaxL1Ball


namespace MinimaxL1Ball

/--
[sqDist_trivialEstimator](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/Cor_5_16.lean)
-/
@[path]
lemma sqDist_trivialEstimator
  {d : ℕ}
  {Y θ : Fin d → ℝ} :
-- imply
  sqDist (trivialEstimator d Y) θ = ∑ i : Fin d, (θ i) ^ 2 := by
-- proof
  simp [sqDist, trivialEstimator, zero_sub]

end MinimaxL1Ball

namespace MinimaxL1Ball

/--
[sum_sq_le_l1norm_sq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/Cor_5_16.lean)
-/
@[path]
lemma sum_sq_le_l1norm_sq
  {d : ℕ}
  {θ : Fin d → ℝ} :
-- imply
  ∑ i : Fin d, (θ i) ^ 2 ≤ l1norm θ ^ 2 := by
-- proof
  simp_rw [(sq_abs (θ _)).symm]
  exact Finset.sum_sq_le_sq_sum_of_nonneg (fun i _ => abs_nonneg _)

end MinimaxL1Ball

namespace MinimaxL1Ball

/--
[sum_sq_le_R_sq_of_l1Ball](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/Cor_5_16.lean)
-/
@[path]
lemma sum_sq_le_R_sq_of_l1Ball
  {d : ℕ}
  {R : ℝ}
  {θ : Fin d → ℝ}
-- given
  (hR : 0 < R)
  (hθ : θ ∈ l1Ball d R) :
-- imply
  ∑ i : Fin d, (θ i) ^ 2 ≤ R ^ 2 := by
-- proof
  calc ∑ i, (θ i) ^ 2 ≤ l1norm θ ^ 2 := sum_sq_le_l1norm_sq θ
    _ ≤ R ^ 2 := by
      apply sq_le_sq'
      · linarith [show (0 : ℝ) ≤ l1norm θ from
        Finset.sum_nonneg (fun i _ => abs_nonneg (θ i))]
      · exact hθ

end MinimaxL1Ball

namespace MinimaxL1Ball

/--
[trivialEstimator_attains](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/Cor_5_16.lean)
-/
@[path]
lemma trivialEstimator_attains
  {d : ℕ}
  {σ R : ℝ}
  {n : ℕ}
  {P : (Fin d → ℝ) → Measure (Fin d → ℝ)}
-- given
  (hσ : 0 < σ)
  (hR : 0 < R)
  (hn : 0 < n)
  (hP : Cor_5_13.IsGSM P σ n)
  (hR_small : R < σ * Real.log ↑d / ↑n) :
-- imply
  ⨆ θ ∈ l1Ball d R, ∫ Y, sqDist (trivialEstimator d Y) θ ∂(P θ) ≤ 2 * min (R ^ 2) (R * σ * Real.log ↑d / ↑n) := by
-- proof
  have h_int : ∀ θ : Fin d → ℝ,
    ∫ Y, sqDist (trivialEstimator d Y) θ ∂(P θ) = ∑ i : Fin d, (θ i) ^ 2 := by
    intro θ
    simp_rw [sqDist_trivialEstimator]
    haveI := hP.isProbabilityMeasure hσ hn θ
    simp [integral_const]
  have h_bound : ⨆ θ ∈ l1Ball d R,
    ∫ Y, sqDist (trivialEstimator d Y) θ ∂(P θ) ≤ R ^ 2 := by
    simp_rw [h_int]
    apply ciSup_le
    intro θ
    by_cases hθ : θ ∈ l1Ball d R
    · haveI : Nonempty (θ ∈ l1Ball d R) := ⟨hθ⟩
      rw [ciSup_const]
      exact sum_sq_le_R_sq_of_l1Ball hR θ hθ
    · have inst : IsEmpty (θ ∈ l1Ball d R) := isEmpty_Prop.mpr hθ
      rw [@Real.iSup_of_isEmpty _ inst]
      positivity
  have h_min_eq : min (R ^ 2) (R * σ * Real.log ↑d / ↑n) = R ^ 2 := by
    apply min_eq_left
    calc R ^ 2 = R * R := by ring
      _ ≤ R * (σ * Real.log ↑d / ↑n) :=
        mul_le_mul_of_nonneg_left (le_of_lt hR_small) (le_of_lt hR)
      _ = R * σ * Real.log ↑d / ↑n := by ring
  calc ⨆ θ ∈ l1Ball d R, ∫ Y, sqDist (trivialEstimator d Y) θ ∂(P θ)
    ≤ R ^ 2 := h_bound
    _ ≤ 2 * R ^ 2 := by linarith [sq_nonneg R]
    _ = 2 * min (R ^ 2) (R * σ * Real.log ↑d / ↑n) := by rw [h_min_eq]

end MinimaxL1Ball

namespace MinimaxL1Ball

/--
[l1norm_scaledBoolVec](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/Cor_5_16.lean)
-/
@[path]
lemma l1norm_scaledBoolVec
  {d : ℕ}
  {ω : Fin d → Bool}
  {s : ℝ}
-- given
  (hs : 0 ≤ s) :
-- imply
  l1norm (Cor_5_13.scaledBoolVec ω s) = s * ↑(InfoTheory.l0norm_bool ω) := by
-- proof
  unfold l1norm Cor_5_13.scaledBoolVec InfoTheory.l0norm_bool
  rw [show Finset.card (Finset.filter (fun i => ω i = true) Finset.univ) =
    ∑ i : Fin d, if ω i = true then 1 else 0 from by rw [Finset.card_filter]]
  push_cast [Finset.mul_sum]
  congr 1; ext i
  cases ω i <;> simp [abs_of_nonneg hs]

end MinimaxL1Ball

namespace MinimaxL1Ball

/--
[scaledBoolVec_in_l1Ball](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/Cor_5_16.lean)
-/
@[path]
lemma scaledBoolVec_in_l1Ball
  {d : ℕ}
  {ω : Fin d → Bool}
  {R : ℝ}
  {k : ℕ}
-- given
  (hR : 0 < R)
  (hk : 0 < k)
  (hweight : InfoTheory.l0norm_bool ω = k) :
-- imply
  Cor_5_13.scaledBoolVec ω (R / ↑k) ∈ l1Ball d R := by
-- proof
  unfold l1Ball
  simp only [Set.mem_setOf_eq]
  rw [l1norm_scaledBoolVec _ _ (le_of_lt (div_pos hR (Nat.cast_pos.mpr hk)))]
  rw [hweight]
  rw [div_mul_cancel₀]
  exact ne_of_gt (Nat.cast_pos.mpr hk)

end MinimaxL1Ball

namespace MinimaxL1Ball

/--
[l1Ball_fano_numerical_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/Cor_5_16.lean)
-/
@[path]
lemma l1Ball_fano_numerical_bound
  {κ : ℝ}
  {M : ℕ}
-- given
  (hM5 : 5 ≤ M)
  (hκ_bound : κ ≤ (1 / 8) * Real.log ((M : ℝ) - 1)) :
-- imply
  (1 : ℝ) - (κ + Real.log 2) / Real.log ((M : ℝ) - 1) ≥ 1 / 4 := by
-- proof
  have hM_ge : (5 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM5
  have hlog_pos : 0 < Real.log ((M : ℝ) - 1) := by
    apply Real.log_pos; linarith
  suffices h : (κ + Real.log 2) / Real.log ((M : ℝ) - 1) ≤ 3 / 4 by linarith
  rw [div_le_iff₀ hlog_pos]
  have hlog4 : Real.log 4 ≤ Real.log ((M : ℝ) - 1) := by
    apply Real.log_le_log (by norm_num : (0 : ℝ) < 4); linarith
  have hlog4_eq : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 from by norm_num, Real.log_pow]; ring
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  nlinarith [hlog4_eq, hlog4, hlog2_pos, hlog_pos]

end MinimaxL1Ball

namespace MinimaxL1Ball

/--
[gsm_kl_scaledBoolVec](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/Cor_5_16.lean)
-/
@[path]
lemma gsm_kl_scaledBoolVec
  {d M : ℕ}
  {P : (Fin d → ℝ) → Measure (Fin d → ℝ)}
  {σ : ℝ}
  {n : ℕ}
  {ω : Fin M → (Fin d → Bool)}
  {s : ℝ}
  {j k : Fin M}
-- given
  (hσ : 0 < σ)
  (hn : 0 < n)
  (hP : Cor_5_13.IsGSM P σ n) :
-- imply
  (klDiv (P (Cor_5_13.scaledBoolVec (ω j) s)) (P (Cor_5_13.scaledBoolVec (ω k) s))).toReal = ↑n * (s ^ 2 * ↑(InfoTheory.hammingDist (ω j) (ω k))) / (2 * σ ^ 2) := by
-- proof
  haveI : ∀ θ, IsProbabilityMeasure (P θ) :=
    fun θ => hP.isProbabilityMeasure hσ hn θ
  rw [InfoTheory.gaussian_kl_divergence _ _ σ hσ n hn P
    (fun θ' i => hP.identity_risk_coord hσ hn θ' i)
    (fun θ₁ θ₂ => hP.density_ratio hσ hn θ₁ θ₂)
    (fun θ' i => hP.coord_mean hσ hn θ' i)]
  congr 1
  rw [Cor_5_13.sqDist_scaledBoolVec]

end MinimaxL1Ball

namespace MinimaxL1Ball

/--
[log_sub_one_ge_half_log](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/Cor_5_16.lean)
-/
@[path]
lemma log_sub_one_ge_half_log
  {M : ℕ}
-- given
  (hM : 5 ≤ M) :
-- imply
  Real.log ((M : ℝ) - 1) ≥ (1 / 2) * Real.log (M : ℝ) := by
-- proof
  have hM_ge5 : (5 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hM_pos : (0 : ℝ) < M := by linarith
  rw [ge_iff_le, ← Real.log_rpow hM_pos]
  apply Real.log_le_log (Real.rpow_pos_of_pos hM_pos _)
  rw [show (M : ℝ) ^ ((1:ℝ)/2) = Real.sqrt M from by rw [Real.sqrt_eq_rpow]]
  rw [← Real.sqrt_sq (by linarith : (0:ℝ) ≤ (M:ℝ) - 1)]
  exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg ((M:ℝ) - 1)])

end MinimaxL1Ball

namespace MinimaxL1Ball

/--
[kl_bound_from_k_squared](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/Cor_5_16.lean)
-/
@[path]
lemma kl_bound_from_k_squared
  {d k : ℕ}
  {n : ℕ}
  {σ R : ℝ}
  {M : ℕ}
-- given
  (hk1 : 1 ≤ k)
  (hσ : 0 < σ)
  (h_ineq : 128 * ↑n * R ^ 2 / σ ^ 2 ≤ (k : ℝ) ^ 2 * Real.log (1 + (d : ℝ) / (2 * (k : ℝ))))
  (hM5 : 5 ≤ M)
  (hlogM : Real.log (M : ℝ) ≥ (k : ℝ) / 8 * Real.log (1 + (d : ℝ) / (2 * (k : ℝ)))) :
-- imply
  ↑n * R ^ 2 / ((k : ℝ) * σ ^ 2) ≤ (1 / 8) * Real.log ((M : ℝ) - 1) := by
-- proof
  have h1 := log_sub_one_ge_half_log hM5
  have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
  have hσ2_pos : (0 : ℝ) < σ ^ 2 := sq_pos_of_pos hσ
  have h_step1 : ↑n * R ^ 2 / ((k : ℝ) * σ ^ 2) ≤
    (k : ℝ) / 128 * Real.log (1 + (d : ℝ) / (2 * (k : ℝ))) := by
    rw [div_le_iff₀ (mul_pos hk_pos hσ2_pos)]
    have h' : 128 * ↑n * R ^ 2 ≤
      (k : ℝ) ^ 2 * Real.log (1 + (d : ℝ) / (2 * (k : ℝ))) * σ ^ 2 := by
      rw [div_le_iff₀ hσ2_pos] at h_ineq; linarith
    nlinarith [sq_nonneg (k : ℝ)]
  calc ↑n * R ^ 2 / ((k : ℝ) * σ ^ 2)
    ≤ (k : ℝ) / 128 * Real.log (1 + (d : ℝ) / (2 * (k : ℝ))) := h_step1
    _ = (1 / 16) * ((k : ℝ) / 8 * Real.log (1 + (d : ℝ) / (2 * (k : ℝ)))) := by ring
    _ ≤ (1 / 16) * Real.log (M : ℝ) := by linarith [hlogM]
    _ = (1 / 8) * ((1 / 2) * Real.log (M : ℝ)) := by ring
    _ ≤ (1 / 8) * Real.log ((M : ℝ) - 1) := by linarith [h1]

end MinimaxL1Ball

namespace MinimaxL1Ball

/--
[fano_parameter_balancing](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/Cor_5_16.lean)
-/
@[path]
lemma fano_parameter_balancing
  {d : ℕ}
  {σ R : ℝ}
  {n : ℕ}
  {ε : ℝ}
-- given
  (hd8 : 8 ≤ d)
  (_hσ : 0 < σ)
  (hR : 0 < R)
  (_hn : 0 < n)
  (_hε : 0 < ε)
  (_hd_large : (d : ℝ) ≥ (n : ℝ) ^ (1 / 2 + ε))
  (h_regime : 128 * ↑n * R ^ 2 / σ ^ 2 ≤ Real.log (1 + ↑d / 2)) :
-- imply
  ∃ (k : ℕ), 1 ≤ k ∧ k ≤ d / 8 ∧ (R ^ 2 / (2 * (k : ℝ)) ≥ 4 * (1 / 2048 * min (R ^ 2) (R * σ * Real.log ↑d / ↑n))) ∧ (128 * ↑n * R ^ 2 / σ ^ 2 ≤ (k : ℝ) ^ 2 * Real.log (1 + (d : ℝ) / (2 * (k : ℝ)))) := by
-- proof
  refine ⟨1, le_refl 1, ?_, ?_, ?_⟩
  · omega
  · simp only [Nat.cast_one, mul_one]
    have hR2 : 0 < R ^ 2 := sq_pos_of_pos hR
    have hmin : min (R ^ 2) (R * σ * Real.log (↑d) / ↑n) ≤ R ^ 2 := min_le_left _ _
    calc R ^ 2 / 2 ≥ R ^ 2 / 512 := by
      apply div_le_div_of_nonneg_left (le_of_lt hR2) (by norm_num) (by norm_num)
      _ = 1 / 512 * R ^ 2 := by ring
      _ ≥ 1 / 512 * min (R ^ 2) (R * σ * Real.log (↑d) / ↑n) := by
        apply mul_le_mul_of_nonneg_left hmin (by norm_num)
      _ = 4 * (1 / 2048 * min (R ^ 2) (R * σ * Real.log (↑d) / ↑n)) := by ring
  · simp only [Nat.cast_one, one_pow, one_mul, mul_one]
    linarith

end MinimaxL1Ball

namespace MinimaxL1Ball

/--
[fano_kl_sparsity_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/Cor_5_16.lean)
-/
@[path]
lemma fano_kl_sparsity_bound
  {d : ℕ}
  {σ R : ℝ}
  {n : ℕ}
  {ε : ℝ}
-- given
  (hd8 : 8 ≤ d)
  (hσ : 0 < σ)
  (hR : 0 < R)
  (hn : 0 < n)
  (hε : 0 < ε)
  (hd_large : (d : ℝ) ≥ (n : ℝ) ^ (1 / 2 + ε))
  (h_regime : 128 * ↑n * R ^ 2 / σ ^ 2 ≤ Real.log (1 + ↑d / 2)) :
-- imply
  ∃ (k : ℕ) (M : ℕ) (_ : 0 < M) (ω : Fin M → (Fin d → Bool)), 1 ≤ k ∧ k ≤ d / 8 ∧ 5 ≤ M ∧ (R ^ 2 / (2 * (k : ℝ)) ≥ 4 * (1 / 2048 * min (R ^ 2) (R * σ * Real.log ↑d / ↑n))) ∧ (↑n * R ^ 2 / ((k : ℝ) * σ ^ 2) ≤ (1 / 8) * Real.log ((M : ℝ) - 1)) ∧ Real.log (M : ℝ) ≥ (k : ℝ) / 8 * Real.log (1 + (d : ℝ) / (2 * (k : ℝ))) ∧ (∀ j : Fin M, InfoTheory.l0norm_bool (ω j) = k) ∧ (∀ j j' : Fin M, j ≠ j' → (InfoTheory.hammingDist (ω j) (ω j') : ℝ) ≥ (k : ℝ) / 2) := by
-- proof
  obtain ⟨k, hk1, hkd, h_sep, h_k2_bound⟩ :=
    fano_parameter_balancing hd8 σ R hσ hR n hn ε hε hd_large h_regime
  obtain ⟨M, hM_pos, ω, hlogM, hM5, hweight, hhamming⟩ :=
    InfoTheory.sparse_varshamov_gilbert d k hk1 hkd
  refine ⟨k, M, hM_pos, ω, hk1, hkd, hM5, h_sep, ?_, hlogM, hweight, hhamming⟩
  exact kl_bound_from_k_squared hk1 hσ h_k2_bound hM5 hlogM

end MinimaxL1Ball

namespace MinimaxL1Ball

/--
[l1Ball_fano_sparsity_choice](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/Cor_5_16.lean)
-/
@[path]
lemma l1Ball_fano_sparsity_choice
  {d : ℕ}
  {σ R : ℝ}
  {n : ℕ}
  {ε : ℝ}
-- given
  (hd8 : 8 ≤ d)
  (hσ : 0 < σ)
  (hR : 0 < R)
  (hn : 0 < n)
  (hε : 0 < ε)
  (hd_large : (d : ℝ) ≥ (n : ℝ) ^ (1 / 2 + ε))
  (h_regime : 128 * ↑n * R ^ 2 / σ ^ 2 ≤ Real.log (1 + ↑d / 2)) :
-- imply
  ∃ (k : ℕ) (M : ℕ) (_ : 0 < M) (ω : Fin M → (Fin d → Bool)), 1 ≤ k ∧ k ≤ d / 8 ∧ 5 ≤ M ∧ (R ^ 2 / (2 * (k : ℝ)) ≥ 4 * (1 / 2048 * min (R ^ 2) (R * σ * Real.log ↑d / ↑n))) ∧ (↑n * R ^ 2 / ((k : ℝ) * σ ^ 2) ≤ (1 / 8) * Real.log ((M : ℝ) - 1)) ∧ Real.log (M : ℝ) ≥ (k : ℝ) / 8 * Real.log (1 + (d : ℝ) / (2 * (k : ℝ))) ∧ (∀ j : Fin M, InfoTheory.l0norm_bool (ω j) = k) ∧ (∀ j j' : Fin M, j ≠ j' → (InfoTheory.hammingDist (ω j) (ω j') : ℝ) ≥ (k : ℝ) / 2) :=
-- proof
  fano_kl_sparsity_bound hd8 σ R hσ hR n hn ε hε hd_large h_regime

end MinimaxL1Ball

namespace MinimaxL1Ball

/--
[l1Ball_fano_parameter_existence](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/Cor_5_16.lean)
-/
@[path]
lemma l1Ball_fano_parameter_existence
  {d : ℕ}
  {σ R : ℝ}
  {n : ℕ}
  {P : (Fin d → ℝ) → Measure (Fin d → ℝ)}
  {ε : ℝ}
-- given
  (hd8 : 8 ≤ d)
  (hσ : 0 < σ)
  (hR : 0 < R)
  (hn : 0 < n)
  (hP : Cor_5_13.IsGSM P σ n)
  (hε : 0 < ε)
  (hd_large : (d : ℝ) ≥ (n : ℝ) ^ (1 / 2 + ε))
  (h_regime : 128 * ↑n * R ^ 2 / σ ^ 2 ≤ Real.log (1 + ↑d / 2)) :
-- imply
  ∃ (M : ℕ) (θ : Fin M → Fin d → ℝ), 2 ≤ M ∧ 5 ≤ M ∧ (∀ j : Fin M, θ j ∈ l1Ball d R) ∧ (∀ j k : Fin M, j ≠ k → InfoTheory.sqDist (θ j) (θ k) ≥ 4 * (1 / 2048 * min (R ^ 2) (R * σ * Real.log ↑d / ↑n))) ∧ (∃ κ : ℝ, κ ≤ (1 / 8) * Real.log ((M : ℝ) - 1) ∧ (1 / (M : ℝ) ^ 2) * ∑ j : Fin M, ∑ k : Fin M, (klDiv (P (θ j)) (P (θ k))).toReal ≤ κ) := by
-- proof
  obtain ⟨k, M, hM_pos, ω, hk1, hkd, hM5, h_sep_bound, h_kl_bound, _hlogM, hweight, hhamming⟩ :=
    l1Ball_fano_sparsity_choice hd8 σ R hσ hR n hn ε hε hd_large h_regime
  let s := R / (k : ℝ)
  let θ : Fin M → Fin d → ℝ := fun j => Cor_5_13.scaledBoolVec (ω j) s
  refine ⟨M, θ, ?_, hM5, ?_, ?_, ?_⟩
  ·
    omega
  ·
    intro j
    exact scaledBoolVec_in_l1Ball (ω j) R k hR (by omega : 0 < k) (hweight j)
  ·
    intro j k' hjk
    have h_sqd : InfoTheory.sqDist (θ j) (θ k') =
      s ^ 2 * ↑(InfoTheory.hammingDist (ω j) (ω k')) :=
      Cor_5_13.sqDist_scaledBoolVec (ω j) (ω k') s
    rw [h_sqd]
    have h_ham := hhamming j k' hjk
    have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr (by omega : 0 < k)
    have hs_eq : s = R / (k : ℝ) := rfl
    have hs_sq : s ^ 2 = R ^ 2 / (k : ℝ) ^ 2 := by
      rw [hs_eq, div_pow]
    calc s ^ 2 * ↑(InfoTheory.hammingDist (ω j) (ω k'))
      ≥ s ^ 2 * ((k : ℝ) / 2) := by
        apply mul_le_mul_of_nonneg_left h_ham (sq_nonneg s)
      _ = R ^ 2 / (k : ℝ) ^ 2 * ((k : ℝ) / 2) := by rw [hs_sq]
      _ = R ^ 2 / (2 * (k : ℝ)) := by field_simp
      _ ≥ 4 * (1 / 2048 * min (R ^ 2) (R * σ * Real.log ↑d / ↑n)) := h_sep_bound
  ·
    refine ⟨↑n * R ^ 2 / ((k : ℝ) * σ ^ 2), ?_, ?_⟩
    ·
      exact h_kl_bound
    ·
      have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr (by omega : 0 < k)
      haveI : ∀ θ', IsProbabilityMeasure (P θ') :=
        fun θ' => hP.isProbabilityMeasure hσ hn θ'
      have hKL_each : ∀ j k' : Fin M,
        (klDiv (P (θ j)) (P (θ k'))).toReal =
        ↑n * (s ^ 2 * ↑(InfoTheory.hammingDist (ω j) (ω k'))) / (2 * σ ^ 2) :=
        fun j k' => gsm_kl_scaledBoolVec P σ hσ n hn hP ω s j k'
      have h_ham_le : ∀ j k' : Fin M,
        (InfoTheory.hammingDist (ω j) (ω k') : ℝ) ≤ 2 * (k : ℝ) := by
        intro j k'
        have hw1 := hweight j
        have hw2 := hweight k'
        have h_card : InfoTheory.hammingDist (ω j) (ω k') ≤ 2 * k := by
          unfold InfoTheory.hammingDist InfoTheory.l0norm_bool at *
          calc (Finset.univ.filter fun i => (ω j) i ≠ (ω k') i).card
            ≤ ((Finset.univ.filter fun i => (ω j) i = true) ∪
              (Finset.univ.filter fun i => (ω k') i = true)).card := by
              apply Finset.card_le_card
              intro i hi
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
              simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
              cases h1 : (ω j) i <;> cases h2 : (ω k') i <;> simp_all
            _ ≤ (Finset.univ.filter fun i => (ω j) i = true).card +
              (Finset.univ.filter fun i => (ω k') i = true).card :=
              Finset.card_union_le _ _
            _ = k + k := by rw [hw1, hw2]
            _ = 2 * k := by ring
        exact_mod_cast h_card
      have hKL_le : ∀ j k' : Fin M,
        (klDiv (P (θ j)) (P (θ k'))).toReal ≤ ↑n * R ^ 2 / ((k : ℝ) * σ ^ 2) := by
        intro j k'
        rw [hKL_each j k']
        have hs_sq : s ^ 2 = R ^ 2 / (k : ℝ) ^ 2 := by
          show (R / (k : ℝ)) ^ 2 = R ^ 2 / (k : ℝ) ^ 2
          rw [div_pow]
        rw [hs_sq]
        have h_ham := h_ham_le j k'
        have hσ2 : (0 : ℝ) < 2 * σ ^ 2 := by positivity
        calc ↑n * (R ^ 2 / (k : ℝ) ^ 2 * ↑(InfoTheory.hammingDist (ω j) (ω k'))) / (2 * σ ^ 2)
          ≤ ↑n * (R ^ 2 / (k : ℝ) ^ 2 * (2 * (k : ℝ))) / (2 * σ ^ 2) := by
            apply div_le_div_of_nonneg_right _ (by positivity : 0 < 2 * σ ^ 2).le
            apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg' n)
            apply mul_le_mul_of_nonneg_left h_ham
            exact div_nonneg (sq_nonneg R) (sq_nonneg (k : ℝ))
          _ = ↑n * R ^ 2 / ((k : ℝ) * σ ^ 2) := by
            field_simp
      have h_sum : (∑ j : Fin M, ∑ k' : Fin M,
        (klDiv (P (θ j)) (P (θ k'))).toReal) ≤
        (M : ℝ) ^ 2 * (↑n * R ^ 2 / ((k : ℝ) * σ ^ 2)) := by
        calc ∑ j : Fin M, ∑ k' : Fin M,
          (klDiv (P (θ j)) (P (θ k'))).toReal
          ≤ ∑ j : Fin M, ∑ _ : Fin M,
            (↑n * R ^ 2 / ((k : ℝ) * σ ^ 2)) := by
            apply Finset.sum_le_sum
            intro j _
            apply Finset.sum_le_sum
            intro k' _
            exact hKL_le j k'
          _ = (M : ℝ) ^ 2 * (↑n * R ^ 2 / ((k : ℝ) * σ ^ 2)) := by
            simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
            ring
      have hM_pos_real : (0 : ℝ) < (M : ℝ) := Nat.cast_pos.mpr hM_pos
      have hM_sq_pos : (0 : ℝ) < (M : ℝ) ^ 2 := by positivity
      calc 1 / (M : ℝ) ^ 2 * ∑ j : Fin M, ∑ k' : Fin M,
        (klDiv (P (θ j)) (P (θ k'))).toReal
        ≤ 1 / (M : ℝ) ^ 2 * ((M : ℝ) ^ 2 * (↑n * R ^ 2 / ((k : ℝ) * σ ^ 2))) := by
          apply mul_le_mul_of_nonneg_left h_sum
          positivity
        _ = ↑n * R ^ 2 / ((k : ℝ) * σ ^ 2) := by
          field_simp

end MinimaxL1Ball

namespace MinimaxL1Ball

/--
[l1Ball_fano_testing_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/Cor_5_16.lean)
-/
@[path]
lemma l1Ball_fano_testing_bound
  {d : ℕ}
  {σ R : ℝ}
  {n : ℕ}
  {P : (Fin d → ℝ) → Measure (Fin d → ℝ)}
  {ε : ℝ}
  {θhat : (Fin d → ℝ) → (Fin d → ℝ)}
-- given
  (hd8 : 8 ≤ d)
  (hσ : 0 < σ)
  (hR : 0 < R)
  (hn : 0 < n)
  (hP : Cor_5_13.IsGSM P σ n)
  (hε : 0 < ε)
  (hd_large : (d : ℝ) ≥ (n : ℝ) ^ (1 / 2 + ε))
  (h_regime : 128 * ↑n * R ^ 2 / σ ^ 2 ≤ Real.log (1 + ↑d / 2))
  (hθhat_meas : Measurable θhat) :
-- imply
  ∃ θ₀ ∈ l1Ball d R, (P θ₀ {Y | sqDist (θhat Y) θ₀ ≥ 1 / 2048 * min (R ^ 2) (R * σ * Real.log ↑d / ↑n)}).toReal ≥ 1 / 4 := by
-- proof
  obtain ⟨M, θ_code, hM2, hM5, h_in_ball, h_sep, κ, hκ_bound, hκ_kl⟩ :=
    l1Ball_fano_parameter_existence hd8 σ R hσ hR n hn P hP ε hε hd_large h_regime
  set ϕ := 1 / 2048 * min (R ^ 2) (R * σ * Real.log ↑d / ↑n) with hϕ_def
  have hlog_pos : 0 < Real.log ↑d := by
    apply Real.log_pos
    have : (1 : ℝ) < ↑d := by exact_mod_cast (show 1 < d by omega)
    exact this
  have hϕ_pos : 0 < ϕ := by
    rw [hϕ_def]
    apply mul_pos (by norm_num : (0 : ℝ) < 1 / 2048)
    apply lt_min (by positivity)
    exact div_pos (mul_pos (mul_pos hR hσ) hlog_pos) (Nat.cast_pos.mpr hn)
  haveI : ∀ θ', IsProbabilityMeasure (P θ') :=
    fun θ' => hP.isProbabilityMeasure hσ hn θ'
  have hac : ∀ j k, P (θ_code j) ≪ P (θ_code k) :=
    fun j k => Cor_5_13.gsm_abs_continuous P σ hσ n hn hP (θ_code j) (θ_code k)
  have h_sep_sq : ∀ j k : Fin M, j ≠ k →
    InfoTheory.sqDist (θ_code j) (θ_code k) ≥ 4 * ϕ :=
    h_sep
  have hM3 : 3 ≤ M := le_trans (by norm_num : 3 ≤ 5) hM5
  have h_fano := InfoTheory.reduction_to_testing_fano hM3 P θ_code hac
    (fun j k => hP.hP_kl_ne_top (θ_code k) (θ_code j))
    ϕ hϕ_pos h_sep_sq κ hκ_kl θhat hθhat_meas
  have h_ge_quarter : (1 : ℝ) - (κ + Real.log 2) / Real.log ((M : ℝ) - 1) ≥ 1 / 4 :=
    l1Ball_fano_numerical_bound κ M hM5 hκ_bound
  have hM_pos : 0 < M := by omega
  haveI : Nonempty (Fin M) := ⟨⟨0, hM_pos⟩⟩
  have h_spec : ⨆ (j : Fin M),
    (P (θ_code j) {Y | InfoTheory.sqDist (θhat Y) (θ_code j) ≥ ϕ}).toReal ≥ 1 / 4 :=
    le_trans h_ge_quarter h_fano
  have h_bdd_above : BddAbove (Set.range fun j : Fin M =>
    (P (θ_code j) {Y | InfoTheory.sqDist (θhat Y) (θ_code j) ≥ ϕ}).toReal) := by
    refine ⟨1, ?_⟩
    rintro x ⟨j, rfl⟩
    exact ENNReal.toReal_le_of_le_ofReal one_pos.le
      (by rw [ENNReal.ofReal_one]; exact prob_le_one)
  obtain ⟨j₀, _, hj₀_max⟩ := Finset.exists_max_image Finset.univ
    (fun j : Fin M => (P (θ_code j) {Y | InfoTheory.sqDist (θhat Y) (θ_code j) ≥ ϕ}).toReal)
    ⟨⟨0, hM_pos⟩, Finset.mem_univ _⟩
  have h_ciSup_le : ⨆ (j : Fin M),
    (P (θ_code j) {Y | InfoTheory.sqDist (θhat Y) (θ_code j) ≥ ϕ}).toReal ≤
    (P (θ_code j₀) {Y | InfoTheory.sqDist (θhat Y) (θ_code j₀) ≥ ϕ}).toReal := by
    apply ciSup_le
    intro j
    exact hj₀_max j (Finset.mem_univ _)
  have h_at_j₀ :
    (P (θ_code j₀) {Y | InfoTheory.sqDist (θhat Y) (θ_code j₀) ≥ ϕ}).toReal ≥ 1 / 4 := by
    linarith
  refine ⟨θ_code j₀, h_in_ball j₀, ?_⟩
  have h_eq : {Y | sqDist (θhat Y) (θ_code j₀) ≥ ϕ} =
    {Y | InfoTheory.sqDist (θhat Y) (θ_code j₀) ≥ ϕ} := by
    ext Y; simp [sqDist, InfoTheory.sqDist]
  rwa [h_eq]

end MinimaxL1Ball

namespace MinimaxL1Ball

/--
[gsm_bddAbove_risk_l1Ball](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/Cor_5_16.lean)
-/
@[path]
lemma gsm_bddAbove_risk_l1Ball
  {d : ℕ}
  {P : (Fin d → ℝ) → Measure (Fin d → ℝ)}
  {σ R : ℝ}
  {n : ℕ}
  {θhat : (Fin d → ℝ) → (Fin d → ℝ)}
-- given
  (hσ : 0 < σ)
  (_hR : 0 < R)
  (hn : 0 < n)
  (hP : Cor_5_13.IsGSM P σ n) :
-- imply
  BddAbove (Set.range fun θ => ⨆ (_ : θ ∈ l1Ball d R), ∫ Y, sqDist (θhat Y) θ ∂(P θ)) := by
-- proof
  have hbdd_univ := Cor_5_13.gsm_bddAbove_risk P σ hσ n hn hP θhat
  obtain ⟨M, hM⟩ := hbdd_univ
  refine ⟨M, ?_⟩
  rintro x ⟨θ, rfl⟩
  show ⨆ (_ : θ ∈ l1Ball d R), ∫ Y, sqDist (θhat Y) θ ∂(P θ) ≤ M
  by_cases hθ : θ ∈ l1Ball d R
  ·
    haveI : Nonempty (θ ∈ l1Ball d R) := ⟨hθ⟩
    rw [ciSup_const]
    have hle : ∫ Y, sqDist (θhat Y) θ ∂(P θ) =
      ∫ Y, Cor_5_13.sqDist (θhat Y) θ ∂(P θ) := by
      congr 1
    rw [hle]
    have h_mem : (⨆ (_ : θ ∈ (Set.univ : Set (Fin d → ℝ))),
      ∫ Y, Cor_5_13.sqDist (θhat Y) θ ∂(P θ)) ∈
      Set.range (fun θ => ⨆ (_ : θ ∈ (Set.univ : Set (Fin d → ℝ))),
        ∫ Y, Cor_5_13.sqDist (θhat Y) θ ∂(P θ)) := Set.mem_range_self θ
    haveI : Nonempty (θ ∈ (Set.univ : Set (Fin d → ℝ))) := ⟨Set.mem_univ θ⟩
    calc ∫ Y, Cor_5_13.sqDist (θhat Y) θ ∂(P θ)
      = ⨆ (_ : θ ∈ (Set.univ : Set (Fin d → ℝ))),
        ∫ Y, Cor_5_13.sqDist (θhat Y) θ ∂(P θ) := (ciSup_const).symm
      _ ≤ M := hM h_mem
  ·
    have inst : IsEmpty (θ ∈ l1Ball d R) := isEmpty_Prop.mpr hθ
    rw [@Real.iSup_of_isEmpty _ inst]
    haveI : Nonempty (θ ∈ (Set.univ : Set (Fin d → ℝ))) := ⟨Set.mem_univ θ⟩
    have hM_ge : M ≥ ∫ Y, Cor_5_13.sqDist (θhat Y) θ ∂(P θ) := by
      calc ∫ Y, Cor_5_13.sqDist (θhat Y) θ ∂(P θ)
        = ⨆ (_ : θ ∈ (Set.univ : Set (Fin d → ℝ))),
          ∫ Y, Cor_5_13.sqDist (θhat Y) θ ∂(P θ) := (ciSup_const).symm
        _ ≤ M := hM (Set.mem_range_self θ)
    calc 0 ≤ ∫ Y, Cor_5_13.sqDist (θhat Y) θ ∂(P θ) :=
      integral_nonneg (fun Y => Finset.sum_nonneg (fun i _ => sq_nonneg _))
      _ ≤ M := hM_ge

end MinimaxL1Ball

namespace MinimaxL1Ball

/--
[fano_minimax_lower_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/Cor_5_16.lean)
-/
@[path]
lemma fano_minimax_lower_bound
  {d : ℕ}
  {P : (Fin d → ℝ) → Measure (Fin d → ℝ)}
  {σ R : ℝ}
  {n : ℕ}
  {ε : ℝ}
-- given
  (hd8 : 8 ≤ d)
  (hσ : 0 < σ)
  (hR : 0 < R)
  (hn : 0 < n)
  (hP : Cor_5_13.IsGSM P σ n)
  (hε : 0 < ε)
  (hd_large : (d : ℝ) ≥ (n : ℝ) ^ (1 / 2 + ε))
  (h_regime : 128 * ↑n * R ^ 2 / σ ^ 2 ≤ Real.log (1 + ↑d / 2)) :
-- imply
  minimaxExpRisk_l1 P R ≥ 1 / 8192 * min (R ^ 2) (R * σ * Real.log d / n) := by
-- proof
  set ϕ := 1 / 2048 * min (R ^ 2) (R * σ * Real.log ↑d / ↑n) with hϕ_def
  have hlog_pos : 0 < Real.log ↑d := by
    apply Real.log_pos
    exact_mod_cast (show 1 < d by omega)
  have hϕ_pos : 0 < ϕ := by
    rw [hϕ_def]
    apply mul_pos (by norm_num : (0 : ℝ) < 1 / 2048)
    apply lt_min (by positivity)
    exact div_pos (mul_pos (mul_pos hR hσ) hlog_pos) (Nat.cast_pos.mpr hn)
  unfold minimaxExpRisk_l1
  rw [ge_iff_le]
  apply le_ciInf
  intro ⟨θhat, hθhat_meas⟩
  have h_test := l1Ball_fano_testing_bound hd8 σ R hσ hR n hn P hP ε hε hd_large h_regime
    θhat hθhat_meas
  obtain ⟨θ₀, hθ₀_mem, hθ₀_prob⟩ := h_test
  have h_bdd := gsm_bddAbove_risk_l1Ball P σ R hσ hR n hn hP θhat
  have h_sup_ge : ⨆ θ ∈ l1Ball d R, ∫ Y, sqDist (θhat Y) θ ∂P θ ≥
    ∫ Y, sqDist (θhat Y) θ₀ ∂P θ₀ := by
    apply le_ciSup_of_le h_bdd θ₀
    rw [ciSup_pos hθ₀_mem]
  have h_int_ge : ∫ Y, sqDist (θhat Y) θ₀ ∂P θ₀ ≥ 1 / 4 * ϕ := by
    have h_integ : Integrable (fun Y => sqDist (θhat Y) θ₀) (P θ₀) := by
      have h : (fun Y => sqDist (θhat Y) θ₀) = (fun Y => Cor_5_13.sqDist (θhat Y) θ₀) := by
        ext Y; simp [sqDist, Cor_5_13.sqDist]
      rw [h]
      exact Cor_5_13.gsm_integrable_sqDist P σ hσ n hn hP θhat θ₀
    have h_nonneg : 0 ≤ᵐ[P θ₀] (fun Y => sqDist (θhat Y) θ₀) :=
      Filter.Eventually.of_forall (fun Y => Finset.sum_nonneg (fun i _ => sq_nonneg _))
    have h_markov := mul_meas_ge_le_integral_of_nonneg h_nonneg h_integ ϕ
    rw [ge_iff_le]
    have h_markov' : ϕ * ((P θ₀) {Y | ϕ ≤ sqDist (θhat Y) θ₀}).toReal ≤
      ∫ Y, sqDist (θhat Y) θ₀ ∂P θ₀ := by
      rwa [← Measure.real_def]
    calc 1 / 4 * ϕ = ϕ * (1 / 4) := by ring
      _ ≤ ϕ * ((P θ₀) {Y | ϕ ≤ sqDist (θhat Y) θ₀}).toReal := by
        gcongr
      _ ≤ ∫ Y, sqDist (θhat Y) θ₀ ∂P θ₀ := h_markov'
  calc 1 / 8192 * min (R ^ 2) (R * σ * Real.log ↑d / ↑n)
    = 1 / 4 * (1 / 2048 * min (R ^ 2) (R * σ * Real.log ↑d / ↑n)) := by ring
    _ = 1 / 4 * ϕ := by rw [hϕ_def]
    _ ≤ ∫ Y, sqDist (θhat Y) θ₀ ∂P θ₀ := h_int_ge
    _ ≤ ⨆ θ ∈ l1Ball d R, ∫ Y, sqDist (θhat Y) θ ∂P θ := h_sup_ge

end MinimaxL1Ball

namespace MinimaxL1Ball

/--
[l1_ball_lower_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/Cor_5_16.lean)
-/
@[path]
lemma l1_ball_lower_bound
  {d : ℕ}
  {σ R : ℝ}
  {n : ℕ}
  {P : (Fin d → ℝ) → Measure (Fin d → ℝ)}
  {ε : ℝ}
-- given
  (hd8 : 8 ≤ d)
  (hσ : 0 < σ)
  (hR : 0 < R)
  (hn : 0 < n)
  (hP : Cor_5_13.IsGSM P σ n)
  (hε : 0 < ε)
  (hd_large : (d : ℝ) ≥ (n : ℝ) ^ (1 / 2 + ε))
  (h_regime : 128 * ↑n * R ^ 2 / σ ^ 2 ≤ Real.log (1 + ↑d / 2)) :
-- imply
  1 / 8192 * min (R ^ 2) (R * σ * Real.log d / n) ≤ minimaxExpRisk_l1 P R :=
-- proof
  fano_minimax_lower_bound P σ R n hd8 hσ hR hn hP ε hε hd_large h_regime

end MinimaxL1Ball

namespace MinimaxL1Ball

/--
[gsm_oracle_inequality_with_width](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/Cor_5_16.lean)
-/
@[path]
lemma gsm_oracle_inequality_with_width
  {d : ℕ}
  {σ R : ℝ}
  {n : ℕ}
  {P : (Fin d → ℝ) → Measure (Fin d → ℝ)}
  {θ : Fin d → ℝ}
  {W : ℝ}
-- given
  (_hd : 0 < d)
  (_hσ : 0 < σ)
  (_hR : 0 < R)
  (_hn : 0 < n)
  (_hP : Cor_5_13.IsGSM P σ n)
  (hθ : θ ∈ l1Ball d R)
  (_hW : W ≥ 0)
  (hW_bound : ∀ θ' ∈ l1Ball d R, ∫ Y, sqDist (constrainedLSEstimator d R Y) θ ∂(P θ) ≤ sqDist θ' θ + W) :
-- imply
  ∫ Y, sqDist (constrainedLSEstimator d R Y) θ ∂(P θ) ≤ (⨅ θ' ∈ l1Ball d R, sqDist θ' θ) + W := by
-- proof
  have h_nonneg : ∀ θ' : Fin d → ℝ, 0 ≤ sqDist θ' θ :=
    fun θ' => Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have h_bdd : BddBelow (⋃ i, Set.range fun (_ : i ∈ l1Ball d R) => sqDist i θ) := by
    use 0
    intro x hx
    simp only [Set.mem_iUnion, Set.mem_range] at hx
    obtain ⟨i, ⟨_, rfl⟩⟩ := hx
    exact h_nonneg i
  have h_le_inf : ∫ Y, sqDist (constrainedLSEstimator d R Y) θ ∂(P θ) - W ≤
    ⨅ θ' ∈ l1Ball d R, sqDist θ' θ := by
    apply le_ciInf
    intro θ'
    by_cases hm : θ' ∈ l1Ball d R
    · haveI : Nonempty (θ' ∈ l1Ball d R) := ⟨hm⟩
      apply le_ciInf
      intro _
      linarith [hW_bound θ' hm]
    · show _ ≤ ⨅ (_ : θ' ∈ l1Ball d R), sqDist θ' θ
      simp only [iInf]
      have : (Set.range fun (_ : θ' ∈ l1Ball d R) => sqDist θ' θ) = ∅ := by
        ext x
        simp only [Set.mem_range, Set.mem_empty_iff_false, iff_false]
        rintro ⟨h, _⟩
        exact hm h
      rw [this, Real.sInf_empty]
      have h_self : sqDist θ θ = 0 := by simp [sqDist, sub_self]
      linarith [hW_bound θ hθ]
  linarith

end MinimaxL1Ball

namespace MinimaxL1Ball

/--
[constrainedLS_l1norm_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/Cor_5_16.lean)
-/
@[path]
lemma constrainedLS_l1norm_le
  {d : ℕ}
  {R : ℝ}
  {Y : Fin d → ℝ}
-- given
  (hR : 0 < R) :
-- imply
  l1norm (constrainedLSEstimator d R Y) ≤ R := by
-- proof
  unfold constrainedLSEstimator
  split
  next h =>
    exact h.choose_spec.1
  next _ =>
    show l1norm (fun _ => 0) ≤ R
    simp [l1norm, abs_of_nonneg]
    linarith

end MinimaxL1Ball

namespace MinimaxL1Ball

/--
[constrainedLS_opt](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/Cor_5_16.lean)
-/
@[path]
lemma constrainedLS_opt
  {d : ℕ}
  {R : ℝ}
  {Y : Fin d → ℝ}
  {u : Fin d → ℝ}
-- given
  (hu : u ∈ l1Ball d R) :
-- imply
  sqDist Y (constrainedLSEstimator d R Y) ≤ sqDist Y u := by
-- proof
  unfold constrainedLSEstimator
  split
  next h =>
    exact h.choose_spec.2 u hu
  next h =>
    exfalso
    apply h
    have hK : IsCompact (l1Ball d R) := by
      rw [Metric.isCompact_iff_isClosed_bounded]
      exact ⟨isClosed_le
        (continuous_finset_sum _ (fun i _ => (continuous_apply i).abs))
        continuous_const,
        Bornology.IsBounded.subset
          (Metric.isBounded_closedBall (x := (0 : Fin d → ℝ)) (r := max R 0))
          (fun θ hθ => by
            simp only [Metric.mem_closedBall, dist_zero_right]
            rw [pi_norm_le_iff_of_nonneg (le_max_right R 0)]
            intro i
            simp only [Real.norm_eq_abs]
            exact le_trans
              (Finset.single_le_sum (fun j _ => abs_nonneg (θ j)) (Finset.mem_univ i))
              (le_trans hθ (le_max_left R 0)))⟩
    have hne : (l1Ball d R).Nonempty := ⟨u, hu⟩
    have hcont : ContinuousOn (sqDist Y) (l1Ball d R) :=
      (continuous_finset_sum _ (fun i _ =>
        (continuous_const.sub (continuous_apply i)).pow 2)).continuousOn
    obtain ⟨x, hx_mem, hx_min⟩ := hK.exists_isMinOn hne hcont
    exact ⟨x, hx_mem, fun θ' hθ' => hx_min hθ'⟩

end MinimaxL1Ball

namespace MinimaxL1Ball

/--
[constrainedLS_pointwise_bound_l1Ball](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/Cor_5_16.lean)
-/
@[path]
lemma constrainedLS_pointwise_bound_l1Ball
  {d : ℕ}
  {σ R : ℝ}
  {n : ℕ}
  {P : (Fin d → ℝ) → Measure (Fin d → ℝ)}
  {θ : Fin d → ℝ}
  {θ' : Fin d → ℝ}
-- given
  (hd : 0 < d)
  (hσ : 0 < σ)
  (hR : 0 < R)
  (hn : 0 < n)
  (hP : Cor_5_13.IsGSM P σ n)
  (_hθ : θ ∈ l1Ball d R)
  (hθ' : θ' ∈ l1Ball d R) :
-- imply
  ∫ Y, sqDist (constrainedLSEstimator d R Y) θ ∂(P θ) ≤ sqDist θ' θ + 2 * (σ ^ 2 / ↑n) * (R * Real.log ↑d / σ) := by
-- proof
  exact hP.cross_term_bound hσ hn hd R hR θ θ'
    (constrainedLSEstimator d R) hθ'
    (fun Y => constrainedLS_l1norm_le R hR Y)
    (fun Y u hu => constrainedLS_opt R Y u hu)

end MinimaxL1Ball

namespace MinimaxL1Ball

/--
[oracle_inequality_constrainedLS_general](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/Cor_5_16.lean)
-/
@[path]
lemma oracle_inequality_constrainedLS_general
  {d : ℕ}
  {σ R : ℝ}
  {n : ℕ}
  {P : (Fin d → ℝ) → Measure (Fin d → ℝ)}
  {θ : Fin d → ℝ}
-- given
  (hd : 0 < d)
  (hσ : 0 < σ)
  (hR : 0 < R)
  (hn : 0 < n)
  (hP : Cor_5_13.IsGSM P σ n)
  (hθ : θ ∈ l1Ball d R) :
-- imply
  ∫ Y, sqDist (constrainedLSEstimator d R Y) θ ∂(P θ) ≤ (⨅ θ' ∈ l1Ball d R, sqDist θ' θ) + 2 * (σ ^ 2 / ↑n) * (R * Real.log ↑d / σ) := by
-- proof
  apply gsm_oracle_inequality_with_width hd σ R hσ hR n hn P hP θ hθ
  · positivity
  · exact fun θ' hθ' =>
    constrainedLS_pointwise_bound_l1Ball hd σ R hσ hR n hn P hP θ hθ θ' hθ'

end MinimaxL1Ball

namespace MinimaxL1Ball

/--
[infimum_sqDist_l1Ball_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/Cor_5_16.lean)
-/
@[path]
lemma infimum_sqDist_l1Ball_zero
  {d : ℕ}
  {R : ℝ}
  {θ : Fin d → ℝ}
-- given
  (hθ : θ ∈ l1Ball d R) :
-- imply
  (⨅ θ' ∈ l1Ball d R, sqDist θ' θ) = 0 := by
-- proof
  have h_self : sqDist θ θ = 0 := by simp [sqDist, sub_self]
  have h_nonneg : ∀ θ' : Fin d → ℝ, 0 ≤ sqDist θ' θ :=
    fun θ' => Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have h_bdd : BddBelow (⋃ i, Set.range fun (_ : i ∈ l1Ball d R) => sqDist i θ) := by
    use 0
    intro x hx
    simp only [Set.mem_iUnion, Set.mem_range] at hx
    obtain ⟨i, ⟨_, rfl⟩⟩ := hx
    exact h_nonneg i
  apply le_antisymm
  · calc ⨅ θ' ∈ l1Ball d R, sqDist θ' θ
    ≤ sqDist θ θ := ciInf₂_le h_bdd θ hθ
    _ = 0 := h_self
  · apply le_ciInf
    intro θ'
    by_cases hm : θ' ∈ l1Ball d R
    · haveI : Nonempty (θ' ∈ l1Ball d R) := ⟨hm⟩
      exact le_ciInf (fun _ => h_nonneg θ')
    ·
      show 0 ≤ ⨅ (_ : θ' ∈ l1Ball d R), sqDist θ' θ
      simp only [iInf]
      convert le_refl (0 : ℝ)
      convert Real.sInf_empty
      ext x
      simp only [Set.mem_range, Set.mem_empty_iff_false, iff_false]
      rintro ⟨h, rfl⟩
      exact hm h

end MinimaxL1Ball

namespace MinimaxL1Ball

/--
[gsm_constrainedLS_oracle_inequality_l1Ball](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/Cor_5_16.lean)
-/
@[path]
lemma gsm_constrainedLS_oracle_inequality_l1Ball
  {d : ℕ}
  {σ R : ℝ}
  {n : ℕ}
  {P : (Fin d → ℝ) → Measure (Fin d → ℝ)}
  {θ : Fin d → ℝ}
-- given
  (hd : 0 < d)
  (hσ : 0 < σ)
  (hR : 0 < R)
  (hn : 0 < n)
  (hP : Cor_5_13.IsGSM P σ n)
  (hθ : θ ∈ l1Ball d R) :
-- imply
  ∫ Y, sqDist (constrainedLSEstimator d R Y) θ ∂(P θ) ≤ 2 * (R * σ * Real.log ↑d / ↑n) := by
-- proof
  have h_oracle := oracle_inequality_constrainedLS_general hd σ R hσ hR n hn P hP θ hθ
  have h_inf_zero := infimum_sqDist_l1Ball_zero R θ hθ
  rw [h_inf_zero] at h_oracle
  have h_eq : 0 + 2 * (σ ^ 2 / ↑n) * (R * Real.log ↑d / σ) =
    2 * (R * σ * Real.log ↑d / ↑n) := by
    field_simp
    ring
  linarith

end MinimaxL1Ball

namespace MinimaxL1Ball

/--
[constrainedLS_risk_pointwise](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/Cor_5_16.lean)
-/
@[path]
lemma constrainedLS_risk_pointwise
  {d : ℕ}
  {σ R : ℝ}
  {n : ℕ}
  {P : (Fin d → ℝ) → Measure (Fin d → ℝ)}
  {_ε : ℝ}
  {θ : Fin d → ℝ}
-- given
  (hd : 0 < d)
  (hσ : 0 < σ)
  (hR : 0 < R)
  (hn : 0 < n)
  (hP : Cor_5_13.IsGSM P σ n)
  (_hε : 0 < _ε)
  (_hd_large : (d : ℝ) ≥ (n : ℝ) ^ (1 / 2 + _ε))
  (hθ : θ ∈ l1Ball d R) :
-- imply
  ∫ Y, sqDist (constrainedLSEstimator d R Y) θ ∂(P θ) ≤ 2 * (R * σ * Real.log ↑d / ↑n) :=
-- proof
  gsm_constrainedLS_oracle_inequality_l1Ball hd σ R hσ hR n hn P hP θ hθ

end MinimaxL1Ball

namespace MinimaxL1Ball

/--
[oracle_inequality_constrainedLS](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/Cor_5_16.lean)
-/
@[path]
lemma oracle_inequality_constrainedLS
  {d : ℕ}
  {σ R : ℝ}
  {n : ℕ}
  {P : (Fin d → ℝ) → Measure (Fin d → ℝ)}
  {ε : ℝ}
-- given
  (hd : 0 < d)
  (hσ : 0 < σ)
  (hR : 0 < R)
  (hn : 0 < n)
  (hP : Cor_5_13.IsGSM P σ n)
  (hε : 0 < ε)
  (hd_large : (d : ℝ) ≥ (n : ℝ) ^ (1 / 2 + ε)) :
-- imply
  ⨆ θ ∈ l1Ball d R, ∫ Y, sqDist (constrainedLSEstimator d R Y) θ ∂(P θ) ≤ 2 * (R * σ * Real.log ↑d / ↑n) := by
-- proof
  apply ciSup_le
  intro θ
  by_cases hθ : θ ∈ l1Ball d R
  · simp only [hθ, ciSup_pos]
    exact constrainedLS_risk_pointwise hd σ R hσ hR n hn P hP ε hε hd_large θ hθ
  · simp only [hθ, ciSup_neg, not_false_eq_true]
    rw [Real.sSup_empty]
    positivity

end MinimaxL1Ball

namespace MinimaxL1Ball

/--
[constrainedLS_attains](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/Cor_5_16.lean)
-/
@[path]
lemma constrainedLS_attains
  {d : ℕ}
  {σ R : ℝ}
  {n : ℕ}
  {P : (Fin d → ℝ) → Measure (Fin d → ℝ)}
  {ε : ℝ}
-- given
  (hd : 0 < d)
  (hσ : 0 < σ)
  (hR : 0 < R)
  (hn : 0 < n)
  (hP : Cor_5_13.IsGSM P σ n)
  (hε : 0 < ε)
  (hd_large : (d : ℝ) ≥ (n : ℝ) ^ (1 / 2 + ε))
  (hR_large : R ≥ σ * Real.log ↑d / ↑n) :
-- imply
  ⨆ θ ∈ l1Ball d R, ∫ Y, sqDist (constrainedLSEstimator d R Y) θ ∂(P θ) ≤ 2 * min (R ^ 2) (R * σ * Real.log ↑d / ↑n) := by
-- proof
  have h_min_eq : min (R ^ 2) (R * σ * Real.log ↑d / ↑n) =
    R * σ * Real.log ↑d / ↑n := by
    apply min_eq_right
    calc R * σ * Real.log ↑d / ↑n
      = R * (σ * Real.log ↑d / ↑n) := by ring
      _ ≤ R * R := by
        apply mul_le_mul_of_nonneg_left hR_large (le_of_lt hR)
      _ = R ^ 2 := by ring
  rw [h_min_eq]
  exact oracle_inequality_constrainedLS hd σ R hσ hR n hn P hP ε hε hd_large

end MinimaxL1Ball

namespace MinimaxL1Ball

/--
[l1_ball_upper_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/Cor_5_16.lean)
-/
@[path]
lemma l1_ball_upper_bound
  {d : ℕ}
  {σ R : ℝ}
  {n : ℕ}
  {P : (Fin d → ℝ) → Measure (Fin d → ℝ)}
  {ε : ℝ}
-- given
  (hd : 0 < d)
  (hσ : 0 < σ)
  (hR : 0 < R)
  (hn : 0 < n)
  (hP : Cor_5_13.IsGSM P σ n)
  (hε : 0 < ε)
  (hd_large : (d : ℝ) ≥ (n : ℝ) ^ (1 / 2 + ε)) :
-- imply
  minimaxExpRisk_l1 P R ≤ 2 * min (R ^ 2) (R * σ * Real.log d / n) := by
-- proof
  unfold minimaxExpRisk_l1
  have h_bdd : BddBelow (Set.range fun (θhat : MeasEstimator d) =>
    ⨆ θ ∈ l1Ball d R, ∫ Y, sqDist (θhat.1 Y) θ ∂(P θ)) := by
    refine ⟨0, ?_⟩
    rintro x ⟨θhat, rfl⟩
    apply Real.iSup_nonneg
    intro θ
    apply Real.iSup_nonneg
    intro _
    exact integral_nonneg (fun Y => Finset.sum_nonneg (fun i _ => sq_nonneg _))
  by_cases hR_case : R ≥ σ * Real.log ↑d / ↑n
  ·
    exact ciInf_le_of_le h_bdd (constrainedLSMeasEstimator d R)
      (constrainedLS_attains hd σ R hσ hR n hn P hP ε hε hd_large hR_case)
  ·
    simp only [not_le] at hR_case
    exact ciInf_le_of_le h_bdd (trivialMeasEstimator d)
      (trivialEstimator_attains σ R hσ hR n hn P hP hR_case)

end MinimaxL1Ball

namespace MinimaxL1Ball

/--
[l1Ball_mono](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/Cor_5_16.lean)
-/
@[path]
lemma l1Ball_mono
  {d : ℕ}
  {R R' : ℝ}
-- given
  (h : R' ≤ R) :
-- imply
  l1Ball d R' ⊆ l1Ball d R :=
-- proof
  fun _ hθ => le_trans hθ h

end MinimaxL1Ball

namespace MinimaxL1Ball

/--
[minimaxExpRisk_l1_mono](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/Cor_5_16.lean)
-/
@[path]
lemma minimaxExpRisk_l1_mono
  {d : ℕ}
  {P : (Fin d → ℝ) → Measure (Fin d → ℝ)}
  {σ : ℝ}
  {n : ℕ}
  {R R' : ℝ}
-- given
  (hσ : 0 < σ)
  (hn : 0 < n)
  (hP : Cor_5_13.IsGSM P σ n)
  (hR : 0 < R)
  (_hR' : 0 < R')
  (hRR' : R' ≤ R) :
-- imply
  minimaxExpRisk_l1 P R' ≤ minimaxExpRisk_l1 P R := by
-- proof
  unfold minimaxExpRisk_l1
  apply ciInf_mono
  ·
    refine ⟨0, ?_⟩
    rintro x ⟨θhat, rfl⟩
    apply Real.iSup_nonneg
    intro θ
    apply Real.iSup_nonneg
    intro _
    exact integral_nonneg (fun Y => Finset.sum_nonneg (fun i _ => sq_nonneg _))
  · intro θhat
    have h_bdd_R := gsm_bddAbove_risk_l1Ball P σ R hσ hR n hn hP θhat.1
    apply ciSup_le
    intro θ
    by_cases hθ : θ ∈ l1Ball d R'
    · simp only [hθ, ciSup_pos]
      have hθR := l1Ball_mono hRR' hθ
      exact le_ciSup_of_le h_bdd_R θ (by
        haveI : Nonempty (θ ∈ l1Ball d R) := ⟨hθR⟩
        rw [ciSup_pos hθR])
    · simp only [hθ, ciSup_neg, not_false_eq_true]
      rw [Real.sSup_empty]
      apply Real.iSup_nonneg
      intro θ'
      apply Real.iSup_nonneg
      intro _
      exact integral_nonneg (fun Y => Finset.sum_nonneg (fun i _ => sq_nonneg _))

end MinimaxL1Ball

namespace MinimaxL1Ball

/--
[cor_5_16](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/Cor_5_16.lean)
-/
@[path]
lemma cor_5_16
  {d : ℕ}
  {σ R : ℝ}
  {n : ℕ}
  {P : (Fin d → ℝ) → Measure (Fin d → ℝ)}
  {ε : ℝ}
-- given
  (hd8 : 8 ≤ d)
  (hσ : 0 < σ)
  (hR : 0 < R)
  (hn : 0 < n)
  (hP : Cor_5_13.IsGSM P σ n)
  (hε : 0 < ε)
  (hd_large : (d : ℝ) ≥ (n : ℝ) ^ (1 / 2 + ε)) :
-- imply
  ∃ (c C : ℝ), 0 < c ∧ 0 < C ∧ c * min (R ^ 2) (R * σ * Real.log d / n) ≤ minimaxExpRisk_l1 P R ∧ minimaxExpRisk_l1 P R ≤ C * min (R ^ 2) (R * σ * Real.log d / n) ∧ (R ≥ σ * Real.log d / n → ⨆ θ ∈ l1Ball d R, ∫ Y, sqDist (constrainedLSEstimator d R Y) θ ∂(P θ) ≤ C * min (R ^ 2) (R * σ * Real.log d / n)) ∧ (R < σ * Real.log d / n → ⨆ θ ∈ l1Ball d R, ∫ Y, sqDist (trivialEstimator d Y) θ ∂(P θ) ≤ C * min (R ^ 2) (R * σ * Real.log d / n)) := by
-- proof
  have hd : 0 < d := by omega
  have hlog_pos : 0 < Real.log ↑d := by
    have : (1 : ℝ) < ↑d := by exact_mod_cast (show 1 < d by omega)
    exact Real.log_pos this
  have hmin_pos : 0 < min (R ^ 2) (R * σ * Real.log ↑d / ↑n) :=
    lt_min (by positivity) (div_pos (mul_pos (mul_pos hR hσ) hlog_pos) (Nat.cast_pos.mpr hn))
  have h_upper := l1_ball_upper_bound hd σ R hσ hR n hn P hP ε hε hd_large
  by_cases h_regime : 128 * ↑n * R ^ 2 / σ ^ 2 ≤ Real.log (1 + ↑d / 2)
  ·
    exact ⟨1 / 8192, 2, by norm_num, by norm_num,
      l1_ball_lower_bound hd8 σ R hσ hR n hn P hP ε hε hd_large h_regime,
      h_upper,
      fun hR_large => constrainedLS_attains hd σ R hσ hR n hn P hP ε hε hd_large hR_large,
      fun hR_small => trivialEstimator_attains σ R hσ hR n hn P hP hR_small⟩
  ·
    simp only [not_le] at h_regime
    set R₀ := σ * Real.sqrt (Real.log (1 + ↑d / 2) / (128 * ↑n)) with hR₀_def
    have hR₀_pos : 0 < R₀ := by
      apply mul_pos hσ (Real.sqrt_pos_of_pos _)
      apply div_pos
      · apply Real.log_pos
        have : (2 : ℝ) ≤ ↑d := by exact_mod_cast (show 2 ≤ d by omega)
        linarith
      · positivity
    have hR₀_lt_R : R₀ < R := by
      have hn_pos : (0 : ℝ) < ↑n := Nat.cast_pos.mpr hn
      have hL_pos : 0 < Real.log (1 + ↑d / 2) := by
        apply Real.log_pos
        have : (2 : ℝ) ≤ ↑d := by exact_mod_cast (show 2 ≤ d by omega)
        linarith
      suffices h : σ ^ 2 * (Real.log (1 + ↑d / 2) / (128 * ↑n)) < R ^ 2 by
        rw [hR₀_def, ← Real.sqrt_sq hσ.le, ← Real.sqrt_mul (sq_nonneg σ),
          ← Real.sqrt_sq hR.le]
        exact Real.sqrt_lt_sqrt (by positivity) h
      have h1 := h_regime
      rw [lt_div_iff₀ (by positivity : (0:ℝ) < σ ^ 2)] at h1
      rw [show σ ^ 2 * (Real.log (1 + ↑d / 2) / (128 * ↑n)) =
        Real.log (1 + ↑d / 2) * σ ^ 2 / (128 * ↑n) from by ring]
      rw [div_lt_iff₀ (by positivity : (0:ℝ) < 128 * ↑n)]
      linarith
    have hR₀_fano : 128 * ↑n * R₀ ^ 2 / σ ^ 2 ≤ Real.log (1 + ↑d / 2) := by
      rw [hR₀_def, mul_pow, Real.sq_sqrt (div_nonneg
        (Real.log_nonneg (by linarith [show (2:ℝ) ≤ ↑d from by exact_mod_cast (show 2 ≤ d by omega)]))
        (by positivity))]
      have h_eq : 128 * ↑n * (σ ^ 2 * (Real.log (1 + ↑d / 2) / (128 * ↑n))) / σ ^ 2 =
        Real.log (1 + ↑d / 2) := by
        field_simp
      linarith
    have h_fano_R₀ : minimaxExpRisk_l1 P R₀ ≥
      1 / 8192 * min (R₀ ^ 2) (R₀ * σ * Real.log ↑d / ↑n) :=
      fano_minimax_lower_bound P σ R₀ n hd8 hσ hR₀_pos hn hP ε hε hd_large hR₀_fano
    have h_mono : minimaxExpRisk_l1 P R₀ ≤ minimaxExpRisk_l1 P R :=
      minimaxExpRisk_l1_mono P σ hσ n hn hP hR hR₀_pos hR₀_lt_R.le
    have h_lb_R₀ : 1 / 8192 * min (R₀ ^ 2) (R₀ * σ * Real.log ↑d / ↑n) ≤
      minimaxExpRisk_l1 P R := le_trans h_fano_R₀ h_mono
    have hmin_R₀_pos : 0 < min (R₀ ^ 2) (R₀ * σ * Real.log ↑d / ↑n) :=
      lt_min (by positivity) (div_pos (mul_pos (mul_pos hR₀_pos hσ) hlog_pos)
        (Nat.cast_pos.mpr hn))
    set c := 1 / 8192 * min (R₀ ^ 2) (R₀ * σ * Real.log ↑d / ↑n) / R ^ 2 with hc_def
    have hc_pos : 0 < c := by positivity
    have h_lower : c * min (R ^ 2) (R * σ * Real.log ↑d / ↑n) ≤
      minimaxExpRisk_l1 P R := by
      calc c * min (R ^ 2) (R * σ * Real.log ↑d / ↑n)
        ≤ c * R ^ 2 := by gcongr; exact min_le_left _ _
        _ = 1 / 8192 * min (R₀ ^ 2) (R₀ * σ * Real.log ↑d / ↑n) := by
          rw [hc_def]; field_simp
        _ ≤ minimaxExpRisk_l1 P R := h_lb_R₀
    exact ⟨c, 2, hc_pos, by norm_num,
      h_lower,
      h_upper,
      fun hR_large => constrainedLS_attains hd σ R hσ hR n hn P hP ε hε hd_large hR_large,
      fun hR_small => trivialEstimator_attains σ R hσ hR n hn P hP hR_small⟩
end MinimaxL1Ball


/--
[measurable_trivialEstimator](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/Cor_5_16.lean)
-/
@[path]
private lemma measurable_trivialEstimator_eq
  {d : ℕ} :
-- imply
  Measurable (trivialEstimator d) := by
-- proof
  apply MinimaxL1Ball.measurable_trivialEstimator d

/--
[isCompact_l1Ball](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/Cor_5_16.lean)
-/
@[path]
private lemma isCompact_l1Ball_eq
  {d : ℕ}
  {R : ℝ} :
-- imply
  IsCompact (l1Ball d R) := by
-- proof
  apply MinimaxL1Ball.isCompact_l1Ball d R

/--
[convex_l1Ball](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/Cor_5_16.lean)
-/
@[path]
private lemma convex_l1Ball_eq
  {d : ℕ}
  {R : ℝ} :
-- imply
  Convex ℝ (l1Ball d R) := by
-- proof
  apply MinimaxL1Ball.convex_l1Ball d R

/--
[midpoint_sqDist](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/Cor_5_16.lean)
-/
@[path]
private lemma midpoint_sqDist_eq
  {d : ℕ}
  {Y θ₁ θ₂ : Fin d → ℝ} :
-- imply
  sqDist Y (fun i => (θ₁ i + θ₂ i) / 2) = (sqDist Y θ₁ + sqDist Y θ₂) / 2 - sqDist θ₁ θ₂ / 4 := by
-- proof
  apply MinimaxL1Ball.midpoint_sqDist Y θ₁ θ₂

/--
[sqDist_pos_of_ne](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/Cor_5_16.lean)
-/
@[path]
private lemma sqDist_pos_of_ne_eq
  {d : ℕ}
  {θ₁ θ₂ : Fin d → ℝ}
-- given
  (h : θ₁ ≠ θ₂) :
-- imply
  0 < sqDist θ₁ θ₂ := by
-- proof
  apply MinimaxL1Ball.sqDist_pos_of_ne h

/--
[unique_minimizer_sqDist](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/Cor_5_16.lean)
-/
@[path]
private lemma unique_minimizer_sqDist_eq
  {d : ℕ}
  {Y : Fin d → ℝ}
  {S : Set (Fin d → ℝ)}
  {θ₁ θ₂ : Fin d → ℝ}
-- given
  (hconv : Convex ℝ S)
  (h0 : θ₁ ∈ S)
  (h1 : θ₂ ∈ S)
  (hmin1 : ∀ θ' ∈ S, sqDist Y θ₁ ≤ sqDist Y θ')
  (hmin2 : ∀ θ' ∈ S, sqDist Y θ₂ ≤ sqDist Y θ') :
-- imply
  θ₁ = θ₂ := by
-- proof
  apply MinimaxL1Ball.unique_minimizer_sqDist Y hconv h0 h1 hmin1 hmin2

/--
[tendsto_sqDist_of_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/Cor_5_16.lean)
-/
@[path]
private lemma tendsto_sqDist_of_tendsto_eq
  {d : ℕ}
  {Ys : ℕ → Fin d → ℝ}
  {Y : Fin d → ℝ}
  {θs : ℕ → Fin d → ℝ}
  {θ : Fin d → ℝ}
-- given
  (hY : Tendsto Ys atTop (𝓝 Y))
  (hθ : Tendsto θs atTop (𝓝 θ)) :
-- imply
  Tendsto (fun n => sqDist (Ys n) (θs n)) atTop (𝓝 (sqDist Y θ)) := by
-- proof
  apply MinimaxL1Ball.tendsto_sqDist_of_tendsto hY hθ

/--
[limit_is_minimizer_sqDist](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/Cor_5_16.lean)
-/
@[path]
private lemma limit_is_minimizer_sqDist_eq
  {d : ℕ}
  {S : Set (Fin d → ℝ)}
  {Ys : ℕ → Fin d → ℝ}
  {Y : Fin d → ℝ}
  {θs : ℕ → Fin d → ℝ}
  {θ : Fin d → ℝ}
  {θ' : Fin d → ℝ}
-- given
  (hY : Tendsto Ys atTop (𝓝 Y))
  (hθ : Tendsto θs atTop (𝓝 θ))
  (hmin : ∀ n, ∀ θ' ∈ S, sqDist (Ys n) (θs n) ≤ sqDist (Ys n) θ')
  (hθ' : θ' ∈ S) :
-- imply
  sqDist Y θ ≤ sqDist Y θ' := by
-- proof
  apply MinimaxL1Ball.limit_is_minimizer_sqDist hY hθ hmin θ' hθ'

/--
[continuous_constrainedLSEstimator](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/Cor_5_16.lean)
-/
@[path]
private lemma continuous_constrainedLSEstimator_eq
  {d : ℕ}
  {R : ℝ} :
-- imply
  Continuous (constrainedLSEstimator d R) := by
-- proof
  apply MinimaxL1Ball.continuous_constrainedLSEstimator d R

/--
[measurable_constrainedLSEstimator](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/Cor_5_16.lean)
-/
@[path]
private lemma measurable_constrainedLSEstimator_eq
  {d : ℕ}
  {R : ℝ} :
-- imply
  Measurable (constrainedLSEstimator d R) := by
-- proof
  apply MinimaxL1Ball.measurable_constrainedLSEstimator d R


-- created on 2026-10-23
