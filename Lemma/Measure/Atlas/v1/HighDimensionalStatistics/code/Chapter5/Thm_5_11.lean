import Mathlib
import sympy.Basic
import Def.v1.Atlas.HighDimensionalStatistics.code.Chapter5.Thm_5_11.Part2
open MeasureTheory InformationTheory Real Finset MinimaxLowerBound


namespace MinimaxLowerBound

/--
[sqDist_eq_infoTheory](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/Thm_5_11.lean)
-/
@[path]
lemma sqDist_eq_infoTheory
  {d : ℕ}
  {θ₁ θ₂ : Fin d → ℝ} :
-- imply
  sqDist θ₁ θ₂ = InfoTheory.sqDist θ₁ θ₂ :=
-- proof
  rfl

end MinimaxLowerBound

namespace MinimaxLowerBound

/--
[fano_algebraic_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/Thm_5_11.lean)
-/
@[path]
lemma fano_algebraic_bound
  {M : ℕ}
  {α : ℝ}
-- given
  (hM : 5 ≤ M)
  (hα_pos : 0 < α) :
-- imply
  (α * Real.log ↑M + Real.log 2) / Real.log (↑M - 1) ≤ 2 * α + 1 / 2 := by
-- proof
  have hM_ge : (5 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hM1_ge : (4 : ℝ) ≤ (↑M : ℝ) - 1 := by linarith
  have hM1_pos : (0 : ℝ) < (↑M : ℝ) - 1 := by linarith
  have hlogM1_pos : 0 < Real.log ((↑M : ℝ) - 1) := by
    apply Real.log_pos; linarith
  have hlog_ratio : Real.log (↑M) ≤ 2 * Real.log ((↑M : ℝ) - 1) := by
    have hle : (↑M : ℝ) ≤ ((↑M : ℝ) - 1) ^ 2 := by nlinarith
    calc Real.log (↑M)
      ≤ Real.log (((↑M : ℝ) - 1) ^ 2) := by
        apply Real.log_le_log (by linarith) hle
      _ = 2 * Real.log ((↑M : ℝ) - 1) := by
        rw [Real.log_pow]
        push_cast
        ring
  have hlog2_bound : Real.log 2 ≤ 1 / 2 * Real.log ((↑M : ℝ) - 1) := by
    have h4 : (4 : ℝ) ≤ (↑M : ℝ) - 1 := hM1_ge
    have : Real.log 4 ≤ Real.log ((↑M : ℝ) - 1) :=
      Real.log_le_log (by norm_num) h4
    have : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 from by norm_num, Real.log_pow]; push_cast; ring
    linarith
  rw [div_le_iff₀ hlogM1_pos]
  calc α * Real.log ↑M + Real.log 2
    ≤ α * (2 * Real.log ((↑M : ℝ) - 1)) + 1 / 2 * Real.log ((↑M : ℝ) - 1) := by
      have := mul_le_mul_of_nonneg_left hlog_ratio (le_of_lt hα_pos)
      linarith
    _ = (2 * α + 1 / 2) * Real.log ((↑M : ℝ) - 1) := by ring

end MinimaxLowerBound

namespace MinimaxLowerBound

/--
[theorem_5_11](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/Thm_5_11.lean)
-/
@[path]
lemma theorem_5_11
  {d : ℕ}
  {M : ℕ}
  {Θ : Set (Fin d → ℝ)}
  {P : (Fin d → ℝ) → Measure (Fin d → ℝ)}
  {θ : Fin M → Fin d → ℝ}
  {σ : ℝ}
  {n : ℕ}
  {α : ℝ}
  {ϕ : ℝ}
  [hprob : ∀ j, IsProbabilityMeasure (P (θ j))]
-- given
  (hM : 5 ≤ M)
  (hθ_mem : ∀ j, θ j ∈ Θ)
  (hσ : 0 < σ)
  (hn : 0 < n)
  (hα_pos : 0 < α)
  (_hα_lt : α < 1 / 4)
  (hϕ : 0 < ϕ)
  (hsep : ∀ j k : Fin M, j ≠ k → sqDist (θ j) (θ k) ≥ 4 * ϕ)
  (hkl : ∀ j k : Fin M, j ≠ k → sqDist (θ j) (θ k) ≤ 2 * α * σ ^ 2 / ↑n * Real.log ↑M)
  (hP_prob : ∀ θ' ∈ Θ, IsProbabilityMeasure (P θ'))
  (hac : ∀ j k, P (θ j) ≪ P (θ k))
  (hfin_kl : ∀ j k, InformationTheory.klDiv (P (θ j)) (P (θ k)) ≠ ⊤)
  (hGSM : ∀ j k : Fin M, (InformationTheory.klDiv (P (θ j)) (P (θ k))).toReal = ↑n * InfoTheory.sqDist (θ j) (θ k) / (2 * σ ^ 2)) :
-- imply
  minimaxRisk P Θ ϕ ≥ 1 / 2 - 2 * α := by
-- proof
  have hM2 : 3 ≤ M := by omega
  have hkl_bound : (1 / (↑M : ℝ) ^ 2) *
    ∑ j : Fin M, ∑ k : Fin M,
      (InformationTheory.klDiv (P (θ j)) (P (θ k))).toReal ≤
    α * Real.log ↑M := by
    have hσ2_pos : 0 < 2 * σ ^ 2 := by positivity
    have hterm : ∀ j k : Fin M,
      (InformationTheory.klDiv (P (θ j)) (P (θ k))).toReal ≤
        α * Real.log ↑M := by
      intro j k
      rw [hGSM j k, ← sqDist_eq_infoTheory]
      by_cases hjk : j = k
      · subst hjk
        simp only [sqDist]
        have : ∑ i : Fin d, (θ j i - θ j i) ^ 2 = 0 := by
          apply Finset.sum_eq_zero; intro i _; simp
        rw [this]; simp
        exact mul_nonneg (le_of_lt hα_pos) (Real.log_nonneg (by exact_mod_cast (show 1 ≤ M by omega)))
      · have h := hkl j k hjk
        have hn_pos : (0 : ℝ) < ↑n := Nat.cast_pos.mpr hn
        calc ↑n * sqDist (θ j) (θ k) / (2 * σ ^ 2)
          ≤ ↑n * (2 * α * σ ^ 2 / ↑n * Real.log ↑M) / (2 * σ ^ 2) := by
            apply div_le_div_of_nonneg_right _ (by positivity)
            exact mul_le_mul_of_nonneg_left h (by positivity)
          _ = α * Real.log ↑M := by field_simp
    have hM_pos : (0 : ℝ) < ↑M := Nat.cast_pos.mpr (by omega)
    calc (1 / (↑M : ℝ) ^ 2) * ∑ j : Fin M, ∑ k : Fin M,
      (InformationTheory.klDiv (P (θ j)) (P (θ k))).toReal
      ≤ (1 / (↑M : ℝ) ^ 2) * ∑ j : Fin M, ∑ k : Fin M, (α * Real.log ↑M) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Finset.sum_le_sum; intro j _
        apply Finset.sum_le_sum; intro k _
        exact hterm j k
      _ = (1 / (↑M : ℝ) ^ 2) * ((↑M : ℝ) * (↑M : ℝ) * (α * Real.log ↑M)) := by
        congr 1
        simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        ring
      _ = α * Real.log ↑M := by
        rw [sq]; field_simp
  have hsep' : ∀ j k : Fin M, j ≠ k → InfoTheory.sqDist (θ j) (θ k) ≥ 4 * ϕ :=
    fun j k hjk => hsep j k hjk
  have halg := fano_algebraic_bound hM hα_pos
  have h_bound : (1 : ℝ) - (α * Real.log ↑M + Real.log 2) /
    Real.log ((↑M : ℝ) - 1) ≥ 1 / 2 - 2 * α := by linarith
  unfold minimaxRisk
  rw [ge_iff_le]
  apply le_ciInf
  intro ⟨θhat, hθhat_meas⟩
  haveI : Nonempty (Fin M) := ⟨⟨0, by omega⟩⟩
  have hfano := @InfoTheory.reduction_to_testing_fano d M hM2 P θ hprob hac hfin_kl
    ϕ hϕ hsep' (α * Real.log ↑M) hkl_bound θhat hθhat_meas
  have h_θhat : 1 / 2 - 2 * α ≤
    ⨆ (j : Fin M), (P (θ j) {Y | InfoTheory.sqDist (θhat Y) (θ j) ≥ ϕ}).toReal := by
    linarith
  have hbdd_biSup : BddAbove (Set.range fun θ' =>
    ⨆ (_ : θ' ∈ Θ), (P θ' {Y | sqDist (θhat Y) θ' ≥ ϕ}).toReal) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨θ', rfl⟩
    simp only
    by_cases hθ' : θ' ∈ Θ
    · haveI := hP_prob θ' hθ'
      rw [ciSup_pos hθ']
      exact ENNReal.toReal_le_of_le_ofReal (by norm_num) (by exact_mod_cast prob_le_one)
    · rw [ciSup_neg hθ']; simp [Real.sSup_empty]
  calc 1 / 2 - 2 * α
    ≤ ⨆ (j : Fin M), (P (θ j) {Y | sqDist (θhat Y) (θ j) ≥ ϕ}).toReal := h_θhat
    _ ≤ ⨆ θ' ∈ Θ, (P θ' {Y | sqDist (θhat Y) θ' ≥ ϕ}).toReal := by
      apply ciSup_le
      intro j
      exact le_ciSup_of_le hbdd_biSup (θ j)
        (le_ciSup_of_le ⟨_, by rintro _ ⟨_, rfl⟩; exact le_refl _⟩ (hθ_mem j) (le_refl _))

end MinimaxLowerBound

namespace MinimaxLowerBound

/--
[hammingDist_le_two_weight](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/Thm_5_11.lean)
-/
@[path]
lemma hammingDist_le_two_weight
  {d : ℕ}
  {k : ℕ}
  {ω₁ ω₂ : Fin d → Bool}
-- given
  (hw₁ : InfoTheory.l0norm_bool ω₁ = k)
  (hw₂ : InfoTheory.l0norm_bool ω₂ = k) :
-- imply
  InfoTheory.hammingDist ω₁ ω₂ ≤ 2 * k := by
-- proof
  simp only [InfoTheory.hammingDist]
  calc (Finset.univ.filter fun i => ω₁ i ≠ ω₂ i).card
    ≤ (Finset.univ.filter fun i => ω₁ i = true).card +
      (Finset.univ.filter fun i => ω₂ i = true).card := by
      apply le_trans (Finset.card_le_card _) (Finset.card_union_le _ _)
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      cases h1 : ω₁ i <;> cases h2 : ω₂ i <;> simp_all
    _ = k + k := by
      simp only [InfoTheory.l0norm_bool] at hw₁ hw₂; rw [hw₁, hw₂]
    _ = 2 * k := by ring

end MinimaxLowerBound

namespace MinimaxLowerBound

/--
[sqDist_scaled_indicator](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/Thm_5_11.lean)
-/
@[path]
lemma sqDist_scaled_indicator
  {d : ℕ}
  {M : ℕ}
  {ω : Fin M → (Fin d → Bool)}
  {scale : ℝ}
  {j k' : Fin M} :
-- imply
  sqDist (fun i => if (ω j i) then scale else 0) (fun i => if (ω k' i) then scale else 0) = scale ^ 2 * (InfoTheory.hammingDist (ω j) (ω k') : ℝ) := by
-- proof
  simp only [sqDist, InfoTheory.hammingDist]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => ω j i ≠ ω k' i)]
  have h_eq_zero : ∑ i ∈ Finset.univ.filter (fun i => ¬(ω j i ≠ ω k' i)),
    ((if ω j i then scale else 0) - (if ω k' i then scale else 0)) ^ 2 = 0 := by
    apply Finset.sum_eq_zero; intro i hi; simp only [Finset.mem_filter, Finset.mem_univ,
      true_and, not_not] at hi; rw [hi]; ring
  rw [h_eq_zero, add_zero]
  have h_each : ∀ i ∈ Finset.univ.filter (fun i => ω j i ≠ ω k' i),
    ((if ω j i then scale else 0) - (if ω k' i then scale else 0)) ^ 2 = scale ^ 2 := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    cases h1 : ω j i <;> cases h2 : ω k' i <;> simp_all
  rw [Finset.sum_congr rfl h_each, Finset.sum_const, Finset.card_filter]
  simp [mul_comm]

end MinimaxLowerBound

namespace MinimaxLowerBound

/--
[l0norm_scaled_indicator](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/Thm_5_11.lean)
-/
@[path]
lemma l0norm_scaled_indicator
  {d : ℕ}
  {ω : Fin d → Bool}
  {scale : ℝ}
-- given
  (hscale : scale ≠ 0) :
-- imply
  l0norm (fun i => if ω i then scale else (0 : ℝ)) = InfoTheory.l0norm_bool ω := by
-- proof
  simp only [l0norm, InfoTheory.l0norm_bool]
  congr 1; ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  cases h : ω i <;> simp [hscale]

end MinimaxLowerBound


-- created on 2026-10-23
