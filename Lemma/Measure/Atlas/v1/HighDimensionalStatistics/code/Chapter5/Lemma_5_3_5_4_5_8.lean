import Mathlib
import sympy.Basic
import Def.v1.Atlas.HighDimensionalStatistics.code.Chapter5.Lemma_5_3_5_4_5_8
open MeasureTheory InformationTheory Chapter5 Chapter5.TVNP


namespace Chapter5.TVNP

/--
[measure_toReal_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/Lemma_5_3_5_4_5_8.lean)
-/
@[path]
lemma measure_toReal_le_one
  [MeasurableSpace Ω]
  {P : Measure Ω}
  [IsProbabilityMeasure P]
  {S : Set Ω} :
-- imply
  (P S).toReal ≤ 1 := by
-- proof
  have h1 : P S ≤ P Set.univ := measure_mono (Set.subset_univ S)
  rw [measure_univ] at h1
  exact ENNReal.toReal_le_of_le_ofReal one_pos.le (by simp [h1])

end Chapter5.TVNP

namespace Chapter5.TVNP

/--
[tvDist_bddAbove](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/Lemma_5_3_5_4_5_8.lean)
-/
@[path]
lemma tvDist_bddAbove
  [MeasurableSpace Ω]
  {P₀ P₁ : Measure Ω}
  [IsProbabilityMeasure P₀]
  [IsProbabilityMeasure P₁] :
-- imply
  BddAbove {x : ℝ | ∃ S : Set Ω, MeasurableSet S ∧ x = |(P₀ S).toReal - (P₁ S).toReal|} := by
-- proof
  use 1; intro x hx; obtain ⟨S, _, hx_eq⟩ := hx; rw [hx_eq]
  have h1 := measure_toReal_le_one P₀ S
  have h2 := measure_toReal_le_one P₁ S
  have h3 : 0 ≤ (P₀ S).toReal := ENNReal.toReal_nonneg
  have h4 : 0 ≤ (P₁ S).toReal := ENNReal.toReal_nonneg
  rw [abs_le]; constructor <;> linarith

end Chapter5.TVNP

namespace Chapter5.TVNP

/--
[tvDist_ge_abs_diff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/Lemma_5_3_5_4_5_8.lean)
-/
@[path]
lemma tvDist_ge_abs_diff
  [MeasurableSpace Ω]
  {P₀ P₁ : Measure Ω}
  [IsProbabilityMeasure P₀]
  [IsProbabilityMeasure P₁]
  {S : Set Ω}
-- given
  (hS : MeasurableSet S) :
-- imply
  |(P₀ S).toReal - (P₁ S).toReal| ≤ tvDist P₀ P₁ := by
-- proof
  apply le_csSup (tvDist_bddAbove P₀ P₁)
  exact ⟨S, hS, rfl⟩

end Chapter5.TVNP

namespace Chapter5.TVNP

/--
[neyman_pearson_lower](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/Lemma_5_3_5_4_5_8.lean)
-/
@[path]
lemma neyman_pearson_lower
  {_ : MeasurableSpace Ω}
  {P₀ P₁ : Measure Ω}
  {ψ : Ω → Bool}
-- given
  (hP₀ : IsProbabilityMeasure P₀)
  (hP₁ : IsProbabilityMeasure P₁)
  (hψ : Measurable ψ) :
-- imply
  (P₀ {ω | ψ ω = true}).toReal + (P₁ {ω | ψ ω = false}).toReal ≥ 1 - tvDist P₀ P₁ := by
-- proof
  have hfalse_meas : MeasurableSet {ω : Ω | ψ ω = false} :=
    hψ (MeasurableSet.singleton false)
  have htrue_eq_compl : {ω : Ω | ψ ω = true} = {ω | ψ ω = false}ᶜ := by
    ext ω; simp only [Set.mem_setOf_eq, Set.mem_compl_iff]; cases ψ ω <;> simp
  have hP₀_compl : (P₀ {ω | ψ ω = true}).toReal =
    1 - (P₀ {ω | ψ ω = false}).toReal := by
    rw [htrue_eq_compl,
      measure_compl hfalse_meas (measure_ne_top P₀ _),
      ENNReal.toReal_sub_of_le (measure_mono (Set.subset_univ _))
        (measure_ne_top P₀ _)]
    simp [measure_univ]
  rw [hP₀_compl]
  have htv := tvDist_ge_abs_diff P₀ P₁ {ω | ψ ω = false} hfalse_meas
  have habs : (P₀ {ω | ψ ω = false}).toReal - (P₁ {ω | ψ ω = false}).toReal ≤
    |(P₀ {ω | ψ ω = false}).toReal - (P₁ {ω | ψ ω = false}).toReal| :=
    le_abs_self _
  linarith

end Chapter5.TVNP

namespace Chapter5.TVNP

/--
[measure_sub_le_on_positive_set](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/Lemma_5_3_5_4_5_8.lean)
-/
@[path]
lemma measure_sub_le_on_positive_set
  {_ : MeasurableSpace Ω}
  {P₀ P₁ ν : Measure Ω}
  [IsProbabilityMeasure P₀]
  [IsProbabilityMeasure P₁]
  [SigmaFinite ν]
  {T : Set Ω}
-- given
  (hν₀ : P₀ ≪ ν)
  (hν₁ : P₁ ≪ ν)
  (hT : MeasurableSet T) :
-- imply
  (P₀ T).toReal - (P₁ T).toReal ≤ (P₀ {ω | P₁.rnDeriv ν ω < P₀.rnDeriv ν ω}).toReal - (P₁ {ω | P₁.rnDeriv ν ω < P₀.rnDeriv ν ω}).toReal := by
-- proof
  set R := {ω : Ω | P₁.rnDeriv ν ω < P₀.rnDeriv ν ω}
  set f := fun ω => (P₀.rnDeriv ν ω).toReal - (P₁.rnDeriv ν ω).toReal
  have hR_meas : MeasurableSet R :=
    measurableSet_lt (Measure.measurable_rnDeriv P₁ ν) (Measure.measurable_rnDeriv P₀ ν)
  have hf_int : Integrable f ν :=
    Integrable.sub Measure.integrable_toReal_rnDeriv Measure.integrable_toReal_rnDeriv
  have h_as_int : ∀ S : Set Ω, MeasurableSet S →
    (P₀ S).toReal - (P₁ S).toReal = ∫ x in S, f x ∂ν := by
    intro S hS; simp only [f]
    rw [integral_sub Measure.integrable_toReal_rnDeriv.integrableOn
      Measure.integrable_toReal_rnDeriv.integrableOn,
      Measure.setIntegral_toReal_rnDeriv hν₀, Measure.setIntegral_toReal_rnDeriv hν₁]; rfl
  rw [h_as_int T hT, h_as_int R hR_meas]
  have hT_split : ∫ x in T, f x ∂ν =
    ∫ x in T ∩ R, f x ∂ν + ∫ x in T ∩ Rᶜ, f x ∂ν := by
    conv_lhs => rw [show T = (T ∩ R) ∪ (T ∩ Rᶜ) from by ext x; simp]
    exact setIntegral_union₀ (Disjoint.aedisjoint disjoint_inf_sdiff)
      (hT.inter hR_meas.compl).nullMeasurableSet hf_int.integrableOn hf_int.integrableOn
  have hR_split : ∫ x in R, f x ∂ν =
    ∫ x in R ∩ T, f x ∂ν + ∫ x in R ∩ Tᶜ, f x ∂ν := by
    conv_lhs => rw [show R = (R ∩ T) ∪ (R ∩ Tᶜ) from by ext x; simp]
    exact setIntegral_union₀ (Disjoint.aedisjoint disjoint_inf_sdiff)
      (hR_meas.inter hT.compl).nullMeasurableSet hf_int.integrableOn hf_int.integrableOn
  rw [hT_split, hR_split, Set.inter_comm T R]
  linarith [
    setIntegral_nonneg_ae (hR_meas.inter hT.compl) (by
      filter_upwards [Measure.rnDeriv_lt_top P₀ ν] with ω hω_top
      intro hω_mem
      simp only [Set.mem_inter_iff, R, Set.mem_setOf_eq] at hω_mem
      exact sub_nonneg.mpr (ENNReal.toReal_mono (ne_top_of_lt hω_top) (le_of_lt hω_mem.1))),
    setIntegral_nonpos_ae (hT.inter hR_meas.compl) (by
      filter_upwards [Measure.rnDeriv_lt_top P₁ ν] with ω hω_top
      intro hω_mem
      simp only [Set.mem_inter_iff, Set.mem_compl_iff, R, Set.mem_setOf_eq, not_lt] at hω_mem
      exact sub_nonpos.mpr (ENNReal.toReal_mono (ne_top_of_lt hω_top) hω_mem.2))
  ]
set_option maxHeartbeats 1200000 in

end Chapter5.TVNP

namespace Chapter5.TVNP

/--
[neyman_pearson_equality](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/Lemma_5_3_5_4_5_8.lean)
-/
@[path]
lemma neyman_pearson_equality
  {_ : MeasurableSpace Ω}
  {P₀ P₁ ν : Measure Ω}
  [SigmaFinite ν]
-- given
  (hP₀ : IsProbabilityMeasure P₀)
  (hP₁ : IsProbabilityMeasure P₁)
  (hν₀ : P₀.AbsolutelyContinuous ν)
  (hν₁ : P₁.AbsolutelyContinuous ν) :
-- imply
  (P₀ {ω | lrTest P₁ P₀ ν ω = true}).toReal + (P₁ {ω | lrTest P₁ P₀ ν ω = false}).toReal = 1 - tvDist P₀ P₁ := by
-- proof
  set R := {ω : Ω | P₁.rnDeriv ν ω < P₀.rnDeriv ν ω}
  have hR_meas : MeasurableSet R :=
    measurableSet_lt (Measure.measurable_rnDeriv P₁ ν) (Measure.measurable_rnDeriv P₀ ν)
  have hR_eq : {ω : Ω | lrTest P₁ P₀ ν ω = false} = R := by
    ext ω; simp [lrTest, not_le, R]
  have hRc_eq : {ω : Ω | lrTest P₁ P₀ ν ω = true} = Rᶜ := by
    ext ω; simp [lrTest, decide_eq_true_eq, R, Set.mem_compl_iff, Set.mem_setOf_eq, not_lt]
  rw [hR_eq, hRc_eq]
  have hP₀c : (P₀ Rᶜ).toReal = 1 - (P₀ R).toReal := by
    rw [measure_compl hR_meas (measure_ne_top P₀ _),
      ENNReal.toReal_sub_of_le (measure_mono (Set.subset_univ _)) (measure_ne_top P₀ _),
      measure_univ, ENNReal.toReal_one]
  rw [hP₀c]
  suffices h : tvDist P₀ P₁ = (P₀ R).toReal - (P₁ R).toReal by linarith
  have hval_nn : 0 ≤ (P₀ R).toReal - (P₁ R).toReal := by
    have hR_int : ∫ x in R, ((P₀.rnDeriv ν x).toReal - (P₁.rnDeriv ν x).toReal) ∂ν =
      (P₀ R).toReal - (P₁ R).toReal := by
      rw [integral_sub Measure.integrable_toReal_rnDeriv.integrableOn
        Measure.integrable_toReal_rnDeriv.integrableOn,
        Measure.setIntegral_toReal_rnDeriv hν₀, Measure.setIntegral_toReal_rnDeriv hν₁]; rfl
    rw [← hR_int]
    exact setIntegral_nonneg_ae hR_meas (by
      filter_upwards [Measure.rnDeriv_lt_top P₀ ν] with ω hω_top hω_mem
      exact sub_nonneg.mpr (ENNReal.toReal_mono (ne_top_of_lt hω_top) (le_of_lt hω_mem)))
  apply le_antisymm
  ·
    simp only [tvDist]
    apply csSup_le
    · exact ⟨|(P₀ Set.univ).toReal - (P₁ Set.univ).toReal|, Set.univ, MeasurableSet.univ, rfl⟩
    intro x hx
    obtain ⟨T, hT_meas, hx_eq⟩ := hx
    rw [hx_eq, abs_le]
    constructor
    ·
      have h_compl := measure_sub_le_on_positive_set P₀ P₁ ν hν₀ hν₁ Tᶜ hT_meas.compl
      have hc₀ : (P₀ Tᶜ).toReal = 1 - (P₀ T).toReal := by
        rw [measure_compl hT_meas (measure_ne_top P₀ _),
          ENNReal.toReal_sub_of_le (measure_mono (Set.subset_univ _)) (measure_ne_top P₀ _),
          measure_univ, ENNReal.toReal_one]
      have hc₁ : (P₁ Tᶜ).toReal = 1 - (P₁ T).toReal := by
        rw [measure_compl hT_meas (measure_ne_top P₁ _),
          ENNReal.toReal_sub_of_le (measure_mono (Set.subset_univ _)) (measure_ne_top P₁ _),
          measure_univ, ENNReal.toReal_one]
      linarith
    ·
      exact measure_sub_le_on_positive_set P₀ P₁ ν hν₀ hν₁ T hT_meas
  ·
    have hab : |(P₀ R).toReal - (P₁ R).toReal| ≤ tvDist P₀ P₁ := by
      apply le_csSup (tvDist_bddAbove P₀ P₁)
      exact ⟨R, hR_meas, rfl⟩
    linarith [abs_of_nonneg hval_nn]

end Chapter5.TVNP

namespace Chapter5.TVNP

/--
[tvDist_eq_infoTheory](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/Lemma_5_3_5_4_5_8.lean)
-/
@[path]
lemma tvDist_eq_infoTheory
  [MeasurableSpace Ω]
  {P Q : Measure Ω} :
-- imply
  tvDist P Q = InfoTheory.tvDist P Q :=
-- proof
  rfl

end Chapter5.TVNP

namespace Chapter5.TVNP

/--
[klDiv_real_eq_infoTheory](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/Lemma_5_3_5_4_5_8.lean)
-/
@[path]
lemma klDiv_real_eq_infoTheory
  [MeasurableSpace Ω]
  {P Q : Measure Ω} :
-- imply
  klDiv_real P Q = InfoTheory.klDiv_real P Q :=
-- proof
  rfl

end Chapter5.TVNP

namespace Chapter5.TVNP

/--
[tvDist_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/Lemma_5_3_5_4_5_8.lean)
-/
@[path]
lemma tvDist_nonneg
  [MeasurableSpace Ω]
  {P Q : Measure Ω}
  [IsProbabilityMeasure P]
  [IsProbabilityMeasure Q] :
-- imply
  0 ≤ tvDist P Q := by
-- proof
  apply le_csSup (tvDist_bddAbove P Q)
  exact ⟨∅, MeasurableSet.empty, by simp⟩

end Chapter5.TVNP

namespace Chapter5.TVNP

/--
[tvDist_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/Lemma_5_3_5_4_5_8.lean)
-/
@[path]
lemma tvDist_le_one
  [MeasurableSpace Ω]
  {P Q : Measure Ω}
  [IsProbabilityMeasure P]
  [IsProbabilityMeasure Q] :
-- imply
  tvDist P Q ≤ 1 := by
-- proof
  apply csSup_le
  · exact ⟨0, ∅, MeasurableSet.empty, by simp⟩
  · intro x ⟨S, _, hx_eq⟩
    rw [hx_eq]
    have h1 := measure_toReal_le_one P S
    have h2 := measure_toReal_le_one Q S
    have h3 : 0 ≤ (P S).toReal := ENNReal.toReal_nonneg
    have h4 : 0 ≤ (Q S).toReal := ENNReal.toReal_nonneg
    rw [abs_le]; constructor <;> linarith

end Chapter5.TVNP

namespace Chapter5.TVNP

/--
[two_sub_two_sqrt_one_sub_ge](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/Lemma_5_3_5_4_5_8.lean)
-/
@[path]
lemma two_sub_two_sqrt_one_sub_ge
  {x : ℝ}
-- given
  (hx1 : x ≤ 1) :
-- imply
  2 - 2 * Real.sqrt (1 - x) ≥ x := by
-- proof
  have h2 : 0 ≤ 1 - x := by linarith
  rw [ge_iff_le, ← sub_nonneg]
  set s := Real.sqrt (1 - x)
  have hs_sq : s * s = 1 - x := Real.mul_self_sqrt h2
  have h4 : 2 - 2 * s - x = (1 - s) * (1 - s) := by nlinarith
  rw [h4]
  exact mul_self_nonneg _

end Chapter5.TVNP

namespace Chapter5.TVNP

/--
[pinsker_inequality](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/Lemma_5_3_5_4_5_8.lean)
-/
@[path]
lemma pinsker_inequality
  {_ : MeasurableSpace Ω}
  {P Q : Measure Ω}
  [IsProbabilityMeasure P]
  [IsProbabilityMeasure Q]
-- given
  (hac : P.AbsolutelyContinuous Q)
  (hKL : klDiv P Q ≠ ⊤) :
-- imply
  tvDist P Q ≤ Real.sqrt (klDiv_real P Q) := by
-- proof
  have h12 : InfoTheory.klDiv_real P Q ≥ 2 - 2 * Real.sqrt (1 - InfoTheory.tvDist P Q ^ 2) :=
    InfoTheory.kl_ge_two_sub_two_sqrt_one_sub_tv_sq P Q hac hKL
  rw [← tvDist_eq_infoTheory, ← klDiv_real_eq_infoTheory] at h12
  have htv_nn := tvDist_nonneg P Q
  have htv_le := tvDist_le_one P Q
  have htv_sq_le : tvDist P Q ^ 2 ≤ 1 := by nlinarith
  have h3 : 2 - 2 * Real.sqrt (1 - tvDist P Q ^ 2) ≥ tvDist P Q ^ 2 :=
    two_sub_two_sqrt_one_sub_ge (tvDist P Q ^ 2) htv_sq_le
  have hkl_ge_tv_sq : klDiv_real P Q ≥ tvDist P Q ^ 2 := by linarith
  rw [← Real.sqrt_sq htv_nn]
  exact Real.sqrt_le_sqrt hkl_ge_tv_sq
set_option maxHeartbeats 1200000 in

end Chapter5.TVNP

namespace Chapter5.TVNP

/--
[neyman_pearson](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/Lemma_5_3_5_4_5_8.lean)
-/
@[path]
lemma neyman_pearson
  {_ : MeasurableSpace Ω}
  {P₀ P₁ ν : Measure Ω}
  [SigmaFinite ν]
-- given
  (hP₀ : IsProbabilityMeasure P₀)
  (hP₁ : IsProbabilityMeasure P₁)
  (hν₀ : P₀.AbsolutelyContinuous ν)
  (hν₁ : P₁.AbsolutelyContinuous ν) :
-- imply
  (∀ (ψ : Ω → Bool) (_hψ : Measurable ψ), (P₀ {ω | ψ ω = true}).toReal + (P₁ {ω | ψ ω = false}).toReal ≥ 1 - tvDist P₀ P₁) ∧ ((P₀ {ω | lrTest P₁ P₀ ν ω = true}).toReal + (P₁ {ω | lrTest P₁ P₀ ν ω = false}).toReal = 1 - tvDist P₀ P₁) :=
-- proof
  ⟨fun ψ hψ => neyman_pearson_lower P₀ P₁ hP₀ hP₁ ψ hψ,
    neyman_pearson_equality P₀ P₁ ν hP₀ hP₁ hν₀ hν₁⟩

end Chapter5.TVNP


-- created on 2026-10-23
