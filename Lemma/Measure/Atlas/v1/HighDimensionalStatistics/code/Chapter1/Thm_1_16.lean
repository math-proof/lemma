import Mathlib
import sympy.Basic
import Theorem.v1.Atlas.HighDimensionalStatistics.code.Chapter1.Thm_1_16
open MeasureTheory Real ProbabilityTheory ENNReal Finset Set SubGaussianPolytope


namespace SubGaussianPolytope

/--
[polytope_sup_subset_vertex_sup](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter1/Thm_1_16.lean)
-/
@[path]
lemma polytope_sup_subset_vertex_sup
  [AddCommGroup E]
  [Module ℝ E]
  {g : Ω → (E →ₗ[ℝ] ℝ)}
  {S : Finset E}
  {t : ℝ} :
-- imply
  {ω | ∃ θ ∈ convexHull ℝ (↑S : Set E), g ω θ > t} ⊆ {ω | ∃ v ∈ S, g ω v > t} := by
-- proof
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢
  obtain ⟨θ, hθ_mem, hθ_gt⟩ := hω
  obtain ⟨v, hv_mem, hv_le⟩ := lemma_1_15_exists_vertex (g ω) S θ hθ_mem
  exact ⟨v, hv_mem, lt_of_lt_of_le hθ_gt hv_le⟩

end SubGaussianPolytope

namespace SubGaussianPolytope

/--
[setOf_bexists_eq_biUnion](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter1/Thm_1_16.lean)
-/
@[path]
lemma setOf_bexists_eq_biUnion
  {S : Finset E}
-- given
  (P : E → Ω → Prop) :
-- imply
  {ω | ∃ v ∈ S, P v ω} = ⋃ v ∈ (S : Set E), {ω | P v ω} := by
-- proof
  ext ω; simp [Set.mem_iUnion]

end SubGaussianPolytope

namespace SubGaussianPolytope

/--
[sup'_equivFin_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter1/Thm_1_16.lean)
-/
@[path]
lemma sup'_equivFin_eq
  {S : Finset E}
  {f : E → ℝ}
-- given
  (hS : S.Nonempty) :
-- imply
  have : Nonempty (Fin S.card) := ⟨⟨0, Finset.card_pos.mpr hS⟩⟩ S.sup' hS f = Finset.univ.sup' Finset.univ_nonempty (fun i => f (S.equivFin.symm i)) := by
-- proof
  haveI : Nonempty (Fin S.card) := ⟨⟨0, Finset.card_pos.mpr hS⟩⟩
  apply le_antisymm
  · apply Finset.sup'_le
    intro v hv
    have hmem : S.equivFin ⟨v, hv⟩ ∈ Finset.univ := Finset.mem_univ _
    have h := Finset.le_sup' (fun i => f (↑(S.equivFin.symm i))) hmem
    simp only [Equiv.symm_apply_apply] at h
    exact h
  · apply Finset.sup'_le
    intro i _
    exact Finset.le_sup' f (S.equivFin.symm i).prop

end SubGaussianPolytope

namespace SubGaussianPolytope

/--
[tail_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter1/Thm_1_16.lean)
-/
@[path]
lemma tail_bound
  [MeasurableSpace Ω]
  {μ : Measure Ω}
  [IsProbabilityMeasure μ]
  [AddCommGroup E]
  [Module ℝ E]
  {g : Ω → (E →ₗ[ℝ] ℝ)}
  {S : Finset E}
  {σsq : ℝ}
  {t : ℝ}
-- given
  (hsg : ∀ v ∈ S, IsSubGaussian (fun ω => g ω v) σsq μ)
  (ht : 0 < t) :
-- imply
  μ {ω | ∃ θ ∈ convexHull ℝ (↑S : Set E), g ω θ > t} ≤ S.card • ENNReal.ofReal (exp (-(t ^ 2 / (2 * σsq)))) := by
-- proof
  have h_subset := polytope_sup_subset_vertex_sup g S t
  calc μ {ω | ∃ θ ∈ convexHull ℝ (↑S : Set E), g ω θ > t}
    ≤ μ {ω | ∃ v ∈ S, g ω v > t} := measure_mono h_subset
    _ = μ (⋃ v ∈ (S : Set E), {ω | g ω v > t}) := by
      congr 1; exact setOf_bexists_eq_biUnion S (fun v ω => g ω v > t)
    _ ≤ ∑' (v : ↥(S : Set E)), μ {ω | g ω (v : E) > t} :=
      measure_biUnion_le μ S.countable_toSet _
    _ ≤ ∑' (_ : ↥(S : Set E)), ENNReal.ofReal (exp (-(t ^ 2 / (2 * σsq)))) := by
      apply ENNReal.tsum_le_tsum
      intro ⟨v, hv⟩
      exact lemma_1_3_upper_tail (hsg v hv) t ht
    _ = S.card • ENNReal.ofReal (exp (-(t ^ 2 / (2 * σsq)))) := by
      rw [tsum_eq_sum (s := Finset.univ) (fun i hi => (hi (Finset.mem_univ i)).elim)]
      simp [Finset.sum_const]

end SubGaussianPolytope

namespace SubGaussianPolytope

/--
[tail_bound'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter1/Thm_1_16.lean)
-/
@[path]
lemma tail_bound'
  [MeasurableSpace Ω]
  {μ : Measure Ω}
  [IsProbabilityMeasure μ]
  [AddCommGroup E]
  [Module ℝ E]
  {g : Ω → (E →ₗ[ℝ] ℝ)}
  {S : Finset E}
  {σsq : ℝ}
  {t : ℝ}
-- given
  (hsg : ∀ v ∈ S, IsSubGaussian (fun ω => g ω v) σsq μ)
  (ht : 0 < t) :
-- imply
  μ {ω | ∃ θ ∈ convexHull ℝ (↑S : Set E), g ω θ > t} ≤ ENNReal.ofReal (S.card * exp (-(t ^ 2 / (2 * σsq)))) := by
-- proof
  calc μ {ω | ∃ θ ∈ convexHull ℝ (↑S : Set E), g ω θ > t}
    ≤ S.card • ENNReal.ofReal (exp (-(t ^ 2 / (2 * σsq)))) :=
      tail_bound g S hsg t ht
    _ = ENNReal.ofReal (S.card * exp (-(t ^ 2 / (2 * σsq)))) := by
      rw [nsmul_eq_mul, ← ENNReal.ofReal_natCast,
        ← ENNReal.ofReal_mul (Nat.cast_nonneg S.card)]

end SubGaussianPolytope

namespace SubGaussianPolytope

/--
[expectation_sup_parametric](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter1/Thm_1_16.lean)
-/
@[path]
lemma expectation_sup_parametric
  [MeasurableSpace Ω]
  {μ : Measure Ω}
  [IsProbabilityMeasure μ]
  [AddCommGroup E]
  [Module ℝ E]
  {g : Ω → (E →ₗ[ℝ] ℝ)}
  {S : Finset E}
  {σsq : ℝ}
  {s : ℝ}
-- given
  (hS : S.Nonempty)
  (hσ : 0 ≤ σsq)
  (hsg : ∀ v ∈ S, IsSubGaussian (fun ω => g ω v) σsq μ)
  (hs : 0 < s) :
-- imply
  ∫ ω, (S.sup' hS (fun v => g ω v)) ∂μ ≤ Real.log S.card / s + σsq * s / 2 := by
-- proof
  let e := S.equivFin
  let X : Fin S.card → Ω → ℝ := fun i ω => g ω (e.symm i)
  have hN : 0 < S.card := Finset.card_pos.mpr hS
  haveI : Nonempty (Fin S.card) := ⟨⟨0, hN⟩⟩
  have hX : ∀ i, IsSubGaussian (X i) σsq μ := by
    intro i; exact hsg (e.symm i) (by simp)
  have h14 := theorem_1_14_expectation_max_parametric hN hσ hX s hs
  suffices hsup : ∀ ω, S.sup' hS (fun v => g ω v) =
    Finset.univ.sup' Finset.univ_nonempty (fun i => X i ω) by
    simp_rw [hsup]; exact h14
  intro ω
  exact sup'_equivFin_eq S hS (fun v => g ω v)

end SubGaussianPolytope

namespace SubGaussianPolytope

/--
[expectation_max_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter1/Thm_1_16.lean)
-/
@[path]
lemma expectation_max_bound
  [MeasurableSpace Ω]
  {μ : Measure Ω}
  [IsProbabilityMeasure μ]
  [AddCommGroup E]
  [Module ℝ E]
  {g : Ω → (E →ₗ[ℝ] ℝ)}
  {S : Finset E}
  {σsq : ℝ}
-- given
  (hS : S.Nonempty)
  (hσ : 0 ≤ σsq)
  (hsg : ∀ v ∈ S, IsSubGaussian (fun ω => g ω v) σsq μ) :
-- imply
  ∫ ω, (S.sup' hS (fun v => g ω v)) ∂μ ≤ Real.sqrt σsq * Real.sqrt (2 * Real.log S.card) := by
-- proof
  by_cases hlog : Real.log (↑S.card : ℝ) ≤ 0
  · have hrhs : Real.sqrt (2 * Real.log ↑S.card) = 0 :=
    Real.sqrt_eq_zero_of_nonpos (by nlinarith)
    rw [hrhs, mul_zero]
    have hcard_pos : 0 < S.card := Finset.card_pos.mpr hS
    have hge : (1 : ℝ) ≤ ↑S.card := by exact_mod_cast hcard_pos
    have hlog_nn : 0 ≤ Real.log (↑S.card : ℝ) := Real.log_nonneg hge
    have hlog_eq : Real.log (↑S.card : ℝ) = 0 := le_antisymm hlog hlog_nn
    have hcard_le : S.card ≤ 1 := by
      by_contra h
      push Not at h
      have : (1 : ℝ) < ↑S.card := by exact_mod_cast h
      linarith [Real.log_pos this]
    have hcard : S.card = 1 := le_antisymm hcard_le hcard_pos
    obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hcard
    subst hv
    simp only [Finset.sup'_singleton]
    linarith [(hsg v (Finset.mem_singleton_self v)).mean_zero]
  · push Not at hlog
    by_cases hσ0 : σsq = 0
    · rw [hσ0, Real.sqrt_zero, zero_mul]
      by_contra hc
      push Not at hc
      set I := ∫ ω, S.sup' hS (fun v => g ω v) ∂μ
      set L := Real.log (↑S.card : ℝ)
      have hL_pos : 0 < L := hlog
      have hI_pos : 0 < I := hc
      have hL_ne : L ≠ 0 := ne_of_gt hL_pos
      have hI_ne : I ≠ 0 := ne_of_gt hI_pos
      have hs_pos : 0 < 2 * L / I := div_pos (by linarith) hI_pos
      have hparam := expectation_sup_parametric g S hS hσ hsg (2 * L / I) hs_pos
      rw [hσ0] at hparam
      simp only [zero_mul, zero_div, add_zero] at hparam
      have hsimp : L / (2 * L / I) = I / 2 := by field_simp
      linarith
    · have hσpos : 0 < σsq := lt_of_le_of_ne hσ (Ne.symm hσ0)
      set L := Real.log (↑S.card : ℝ) with hL_def
      set s₀ := Real.sqrt (2 * L / σsq) with hs₀_def
      have h2Lb : 0 < 2 * L / σsq := div_pos (by linarith) hσpos
      have hs₀_pos : 0 < s₀ := Real.sqrt_pos_of_pos h2Lb
      have hparam := expectation_sup_parametric g S hS hσ hsg s₀ hs₀_pos
      suffices hopt : L / s₀ + σsq * s₀ / 2 = Real.sqrt σsq * Real.sqrt (2 * L) by
        linarith
      have hs₀_sq : s₀ ^ 2 = 2 * L / σsq := Real.sq_sqrt (le_of_lt h2Lb)
      have hL_eq : L = σsq * s₀ ^ 2 / 2 := by field_simp at hs₀_sq ⊢; linarith
      have hterm : L / s₀ = σsq * s₀ / 2 := by rw [hL_eq]; field_simp
      have hsum : L / s₀ + σsq * s₀ / 2 = σsq * s₀ := by linarith
      have h2L_eq : 2 * L = σsq * s₀ ^ 2 := by linarith
      have hrhs : Real.sqrt σsq * Real.sqrt (2 * L) = σsq * s₀ := by
        rw [show 2 * L = σsq * s₀ ^ 2 from h2L_eq]
        rw [Real.sqrt_mul hσ, Real.sqrt_sq (le_of_lt hs₀_pos)]
        rw [← mul_assoc, Real.mul_self_sqrt hσ]
      linarith

end SubGaussianPolytope

namespace SubGaussianPolytope

/--
[expectation_abs_sup_parametric](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter1/Thm_1_16.lean)
-/
@[path]
lemma expectation_abs_sup_parametric
  [MeasurableSpace Ω]
  {μ : Measure Ω}
  [IsProbabilityMeasure μ]
  [AddCommGroup E]
  [Module ℝ E]
  {g : Ω → (E →ₗ[ℝ] ℝ)}
  {S : Finset E}
  {σsq : ℝ}
  {s : ℝ}
-- given
  (hS : S.Nonempty)
  (hσ : 0 ≤ σsq)
  (hsg : ∀ v ∈ S, IsSubGaussian (fun ω => g ω v) σsq μ)
  (hs : 0 < s) :
-- imply
  ∫ ω, (S.sup' hS (fun v => |g ω v|)) ∂μ ≤ Real.log (2 * S.card) / s + σsq * s / 2 := by
-- proof
  let e := S.equivFin
  let X : Fin S.card → Ω → ℝ := fun i ω => g ω (e.symm i)
  have hN : 0 < S.card := Finset.card_pos.mpr hS
  haveI : Nonempty (Fin S.card) := ⟨⟨0, hN⟩⟩
  have hX : ∀ i, IsSubGaussian (X i) σsq μ := by
    intro i; exact hsg (e.symm i) (by simp)
  have h14 := theorem_1_14_expectation_abs_max_parametric hN hσ hX s hs
  suffices hsup : ∀ ω, S.sup' hS (fun v => |g ω v|) =
    Finset.univ.sup' Finset.univ_nonempty (fun i => |X i ω|) by
    simp_rw [hsup]; exact h14
  intro ω
  exact sup'_equivFin_eq S hS (fun v => |g ω v|)

end SubGaussianPolytope

namespace SubGaussianPolytope

/--
[expectation_abs_max_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter1/Thm_1_16.lean)
-/
@[path]
lemma expectation_abs_max_bound
  [MeasurableSpace Ω]
  {μ : Measure Ω}
  [IsProbabilityMeasure μ]
  [AddCommGroup E]
  [Module ℝ E]
  {g : Ω → (E →ₗ[ℝ] ℝ)}
  {S : Finset E}
  {σsq : ℝ}
-- given
  (hS : S.Nonempty)
  (hσ : 0 ≤ σsq)
  (hsg : ∀ v ∈ S, IsSubGaussian (fun ω => g ω v) σsq μ) :
-- imply
  ∫ ω, (S.sup' hS (fun v => |g ω v|)) ∂μ ≤ Real.sqrt σsq * Real.sqrt (2 * Real.log (2 * S.card)) := by
-- proof
  have hN : 0 < S.card := Finset.card_pos.mpr hS
  by_cases hσ0 : σsq = 0
  · rw [hσ0, Real.sqrt_zero, zero_mul]
    by_contra hc
    push Not at hc
    set I := ∫ ω, S.sup' hS (fun v => |g ω v|) ∂μ
    set L := Real.log (2 * (↑S.card : ℝ))
    have hL_pos : 0 < L := by
      apply Real.log_pos
      exact_mod_cast (show 1 < 2 * S.card by omega)
    have hI_pos : 0 < I := hc
    have hL_ne : L ≠ 0 := ne_of_gt hL_pos
    have hI_ne : I ≠ 0 := ne_of_gt hI_pos
    have hs_pos : 0 < 2 * L / I := div_pos (by linarith) hI_pos
    have hparam := expectation_abs_sup_parametric g S hS hσ hsg (2 * L / I) hs_pos
    rw [hσ0] at hparam
    simp only [zero_mul, zero_div, add_zero] at hparam
    have hsimp : L / (2 * L / I) = I / 2 := by field_simp
    linarith
  · have hσpos : 0 < σsq := lt_of_le_of_ne hσ (Ne.symm hσ0)
    have h2N_pos : (1 : ℝ) < 2 * ↑S.card := by
      exact_mod_cast (show 1 < 2 * S.card by omega)
    have hlog2N : 0 < Real.log (2 * (S.card : ℝ)) := Real.log_pos h2N_pos
    set L := Real.log (2 * (S.card : ℝ)) with hL_def
    set s₀ := Real.sqrt (2 * L / σsq) with hs₀_def
    have h2Lb : 0 < 2 * L / σsq := div_pos (by linarith) hσpos
    have hs₀_pos : 0 < s₀ := Real.sqrt_pos_of_pos h2Lb
    have hparam := expectation_abs_sup_parametric g S hS hσ hsg s₀ hs₀_pos
    suffices hopt : L / s₀ + σsq * s₀ / 2 = Real.sqrt σsq * Real.sqrt (2 * L) by
      linarith
    have hs₀_sq : s₀ ^ 2 = 2 * L / σsq := Real.sq_sqrt (le_of_lt h2Lb)
    have hL_eq : L = σsq * s₀ ^ 2 / 2 := by field_simp at hs₀_sq ⊢; linarith
    have hterm : L / s₀ = σsq * s₀ / 2 := by rw [hL_eq]; field_simp
    have hsum : L / s₀ + σsq * s₀ / 2 = σsq * s₀ := by linarith
    have h2L_eq : 2 * L = σsq * s₀ ^ 2 := by linarith
    have hrhs : Real.sqrt σsq * Real.sqrt (2 * L) = σsq * s₀ := by
      rw [show 2 * L = σsq * s₀ ^ 2 from h2L_eq]
      rw [Real.sqrt_mul hσ, Real.sqrt_sq (le_of_lt hs₀_pos)]
      rw [← mul_assoc, Real.mul_self_sqrt hσ]
    linarith

end SubGaussianPolytope

namespace SubGaussianPolytope

/--
[polytope_abs_sup_subset_vertex_abs_sup](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter1/Thm_1_16.lean)
-/
@[path]
lemma polytope_abs_sup_subset_vertex_abs_sup
  [AddCommGroup E]
  [Module ℝ E]
  {g : Ω → (E →ₗ[ℝ] ℝ)}
  {S : Finset E}
  {t : ℝ} :
-- imply
  {ω | ∃ θ ∈ convexHull ℝ (↑S : Set E), |g ω θ| > t} ⊆ {ω | ∃ v ∈ S, |g ω v| > t} := by
-- proof
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢
  obtain ⟨θ, hθ_mem, hθ_gt⟩ := hω
  rw [GT.gt, lt_abs] at hθ_gt
  obtain hpos | hneg := hθ_gt
  ·
    obtain ⟨v, hv_mem, hv_le⟩ := lemma_1_15_exists_vertex (g ω) S θ hθ_mem
    refine ⟨v, hv_mem, ?_⟩
    rw [GT.gt, lt_abs]
    left; linarith
  ·
    obtain ⟨v, hv_mem, hv_le⟩ := lemma_1_15_exists_vertex (-(g ω)) S θ hθ_mem
    simp only [LinearMap.neg_apply] at hv_le
    refine ⟨v, hv_mem, ?_⟩
    rw [GT.gt, lt_abs]
    right; linarith

end SubGaussianPolytope

namespace SubGaussianPolytope

/--
[abs_tail_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter1/Thm_1_16.lean)
-/
@[path]
lemma abs_tail_bound
  [MeasurableSpace Ω]
  {μ : Measure Ω}
  [IsProbabilityMeasure μ]
  [AddCommGroup E]
  [Module ℝ E]
  {g : Ω → (E →ₗ[ℝ] ℝ)}
  {S : Finset E}
  {σsq : ℝ}
  {t : ℝ}
-- given
  (hsg : ∀ v ∈ S, IsSubGaussian (fun ω => g ω v) σsq μ)
  (ht : 0 < t) :
-- imply
  μ {ω | ∃ θ ∈ convexHull ℝ (↑S : Set E), |g ω θ| > t} ≤ ENNReal.ofReal (2 * ↑S.card * exp (-(t ^ 2 / (2 * σsq)))) := by
-- proof
  have h_subset := polytope_abs_sup_subset_vertex_abs_sup g S t
  have h_vertex : μ {ω | ∃ v ∈ S, |g ω v| > t} ≤
    ENNReal.ofReal (2 * ↑S.card * exp (-(t ^ 2 / (2 * σsq)))) := by
    let e := S.equivFin
    let X : Fin S.card → Ω → ℝ := fun i ω => g ω (e.symm i)
    have hX : ∀ i, IsSubGaussian (X i) σsq μ := by
      intro i; exact hsg (e.symm i) (by simp)
    have h14 := subGaussian_max_abs_tail_prob hX t ht
    suffices h_eq : {ω | ∃ v ∈ S, |g ω v| > t} ⊆
      {ω | ∃ i, |X i ω| > t} by
      exact le_trans (measure_mono h_eq) h14
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    obtain ⟨v, hv, hvt⟩ := hω
    exact ⟨e ⟨v, hv⟩, by
      show |g ω ↑(e.symm (e ⟨v, hv⟩))| > t
      have : (e.symm (e ⟨v, hv⟩) : E) = v :=
        congr_arg Subtype.val (Equiv.symm_apply_apply e ⟨v, hv⟩)
      rw [this]
      exact hvt⟩
  exact le_trans (measure_mono h_subset) h_vertex

end SubGaussianPolytope

namespace SubGaussianPolytope

/--
[theorem_1_16](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter1/Thm_1_16.lean)
-/
@[path]
lemma theorem_1_16
  [MeasurableSpace Ω]
  {μ : Measure Ω}
  [IsProbabilityMeasure μ]
  [AddCommGroup E]
  [Module ℝ E]
  {g : Ω → (E →ₗ[ℝ] ℝ)}
  {S : Finset E}
  {σsq : ℝ}
  {t : ℝ}
-- given
  (hS : S.Nonempty)
  (hσ : 0 ≤ σsq)
  (hsg : ∀ v ∈ S, IsSubGaussian (fun ω => g ω v) σsq μ)
  (ht : 0 < t) :
-- imply
  (∫ ω, (S.sup' hS (fun v => g ω v)) ∂μ ≤ Real.sqrt σsq * Real.sqrt (2 * Real.log S.card)) ∧ (∫ ω, (S.sup' hS (fun v => |g ω v|)) ∂μ ≤ Real.sqrt σsq * Real.sqrt (2 * Real.log (2 * S.card))) ∧ (μ {ω | ∃ θ ∈ convexHull ℝ (↑S : Set E), g ω θ > t} ≤ S.card • ENNReal.ofReal (exp (-(t ^ 2 / (2 * σsq))))) ∧ (μ {ω | ∃ θ ∈ convexHull ℝ (↑S : Set E), |g ω θ| > t} ≤ ENNReal.ofReal (2 * ↑S.card * exp (-(t ^ 2 / (2 * σsq))))) :=
-- proof
  ⟨expectation_max_bound g S hS hσ hsg,
    expectation_abs_max_bound g S hS hσ hsg,
    tail_bound g S hsg t ht,
    abs_tail_bound g S hsg t ht⟩

end SubGaussianPolytope

/--
[theorem_1_16_polytope_subgaussian](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter1/Thm_1_16.lean)
-/
@[path]
lemma theorem_1_16_polytope_subgaussian
  [MeasurableSpace Ω]
  {μ : Measure Ω}
  [IsProbabilityMeasure μ]
  [AddCommGroup E]
  [Module ℝ E]
  {g : Ω → (E →ₗ[ℝ] ℝ)}
  {S : Finset E}
  {σsq : ℝ}
  {t : ℝ}
-- given
  (hsg : ∀ v ∈ S, IsSubGaussian (fun ω => g ω v) σsq μ)
  (ht : 0 < t) :
-- imply
  μ {ω | ∃ θ ∈ convexHull ℝ (↑S : Set E), g ω θ > t} ≤ S.card • ENNReal.ofReal (exp (-(t ^ 2 / (2 * σsq)))) :=
-- proof
  SubGaussianPolytope.tail_bound g S hsg t ht

/--
[theorem_1_16_polytope_subgaussian'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter1/Thm_1_16.lean)
-/
@[path]
lemma theorem_1_16_polytope_subgaussian'
  [MeasurableSpace Ω]
  {μ : Measure Ω}
  [IsProbabilityMeasure μ]
  [AddCommGroup E]
  [Module ℝ E]
  {g : Ω → (E →ₗ[ℝ] ℝ)}
  {S : Finset E}
  {σsq : ℝ}
  {t : ℝ}
-- given
  (hsg : ∀ v ∈ S, IsSubGaussian (fun ω => g ω v) σsq μ)
  (ht : 0 < t) :
-- imply
  μ {ω | ∃ θ ∈ convexHull ℝ (↑S : Set E), g ω θ > t} ≤ ENNReal.ofReal (S.card * exp (-(t ^ 2 / (2 * σsq)))) :=
-- proof
  SubGaussianPolytope.tail_bound' g S hsg t ht

/--
[theorem_1_16_expectation_max](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter1/Thm_1_16.lean)
-/
@[path]
lemma theorem_1_16_expectation_max
  [MeasurableSpace Ω]
  {μ : Measure Ω}
  [IsProbabilityMeasure μ]
  [AddCommGroup E]
  [Module ℝ E]
  {g : Ω → (E →ₗ[ℝ] ℝ)}
  {S : Finset E}
  {σsq : ℝ}
-- given
  (hS : S.Nonempty)
  (hσ : 0 ≤ σsq)
  (hsg : ∀ v ∈ S, IsSubGaussian (fun ω => g ω v) σsq μ) :
-- imply
  ∫ ω, (S.sup' hS (fun v => g ω v)) ∂μ ≤ Real.sqrt σsq * Real.sqrt (2 * Real.log S.card) :=
-- proof
  SubGaussianPolytope.expectation_max_bound g S hS hσ hsg

/--
[theorem_1_16_expectation_abs_max](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter1/Thm_1_16.lean)
-/
@[path]
lemma theorem_1_16_expectation_abs_max
  [MeasurableSpace Ω]
  {μ : Measure Ω}
  [IsProbabilityMeasure μ]
  [AddCommGroup E]
  [Module ℝ E]
  {g : Ω → (E →ₗ[ℝ] ℝ)}
  {S : Finset E}
  {σsq : ℝ}
-- given
  (hS : S.Nonempty)
  (hσ : 0 ≤ σsq)
  (hsg : ∀ v ∈ S, IsSubGaussian (fun ω => g ω v) σsq μ) :
-- imply
  ∫ ω, (S.sup' hS (fun v => |g ω v|)) ∂μ ≤ Real.sqrt σsq * Real.sqrt (2 * Real.log (2 * S.card)) :=
-- proof
  SubGaussianPolytope.expectation_abs_max_bound g S hS hσ hsg


-- created on 2026-10-23
