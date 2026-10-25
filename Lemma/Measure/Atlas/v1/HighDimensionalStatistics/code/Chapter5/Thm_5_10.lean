import Mathlib
import sympy.Basic
import Def.v1.Atlas.HighDimensionalStatistics.code.Chapter5.Thm_5_10
open MeasureTheory InformationTheory Finset Real FanoInequality


namespace FanoInequality

/--
[mixtureMeasure_eq_infoTheory](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/Thm_5_10.lean)
-/
@[path]
lemma mixtureMeasure_eq_infoTheory
  [MeasurableSpace Ω]
  {M : ℕ}
  {P : Fin M → Measure Ω} :
-- imply
  mixtureMeasure P = InfoTheory.mixtureMeasure M P := by
-- proof
  unfold mixtureMeasure InfoTheory.mixtureMeasure
  rw [one_div]

end FanoInequality

namespace FanoInequality

/--
[fano_lemma](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/Thm_5_10.lean)
-/
@[path]
lemma fano_lemma
  [MeasurableSpace Ω]
  {M : ℕ}
  {P : Fin M → Measure Ω}
  [∀ j, IsProbabilityMeasure (P j)]
-- given
  (hM : 3 ≤ M)
  (hac : ∀ j k, P j ≪ P k)
  (hfin : ∀ j k, klDiv (P j) (P k) ≠ ⊤) :
-- imply
  ∀ (ψ : Ω → Fin M), Measurable ψ → ∃ j : Fin M, (P j {ω | ψ ω ≠ j}).toReal ≥ 1 - ((1 / (M : ℝ)) * ∑ j : Fin M, (klDiv (P j) (mixtureMeasure P)).toReal + Real.log 2) / Real.log ((M : ℝ) - 1) := by
-- proof
  intro ψ hψ
  simp_rw [mixtureMeasure_eq_infoTheory]
  have hfin_kl : ∀ j, klDiv (P j) (InfoTheory.mixtureMeasure M P) ≠ ⊤ :=
    fun j => InfoTheory.klDiv_mixture_ne_top M (by omega) P hac hfin j
  exact InfoTheory.fano_lemma M hM P hfin_kl ψ hψ

end FanoInequality

namespace FanoInequality

/--
[kl_mixture_le_avg_pairwise](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/Thm_5_10.lean)
-/
@[path]
lemma kl_mixture_le_avg_pairwise
  [MeasurableSpace Ω]
  {M : ℕ}
  {P : Fin M → Measure Ω}
  [∀ j, IsProbabilityMeasure (P j)]
-- given
  (hM : 2 ≤ M)
  (hac : ∀ j k, P j ≪ P k)
  (hfin : ∀ j k, klDiv (P j) (P k) ≠ ⊤) :
-- imply
  (1 / (M : ℝ)) * ∑ j : Fin M, (klDiv (P j) (mixtureMeasure P)).toReal ≤ (1 / (M : ℝ) ^ 2) * ∑ j : Fin M, ∑ k : Fin M, (klDiv (P j) (P k)).toReal := by
-- proof
  simp_rw [mixtureMeasure_eq_infoTheory]
  exact InfoTheory.kl_mixture_le_avg_pairwise M hM P hac hfin

end FanoInequality

namespace FanoInequality

/--
[fano_avg_numerator_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/Thm_5_10.lean)
-/
@[path]
lemma fano_avg_numerator_bound
  [MeasurableSpace Ω]
  {M : ℕ}
  {P : Fin M → Measure Ω}
  [∀ j, IsProbabilityMeasure (P j)]
  {ψ : Ω → Fin M}
-- given
  (hM : 2 ≤ M)
  (hac : ∀ j k, P j ≪ P k)
  (hfin : ∀ j k, klDiv (P j) (P k) ≠ ⊤)
  (hψ : Measurable ψ) :
-- imply
  ((1 / (M : ℝ)) * ∑ j : Fin M, (P j {ω | ψ ω ≠ j}).toReal) * Real.log ((M : ℝ) - 1) + Real.log 2 ≥ Real.log (M : ℝ) - (1 / (M : ℝ) ^ 2) * ∑ j : Fin M, ∑ k : Fin M, (klDiv (P j) (P k)).toReal := by
-- proof
  have hfin_kl : ∀ j, klDiv (P j) (InfoTheory.mixtureMeasure M P) ≠ ⊤ :=
    fun j => InfoTheory.klDiv_mixture_ne_top M hM P hac hfin j
  have h_core := InfoTheory.fano_entropy_core_bound M hM P hfin_kl ψ hψ
  have h_kl : (1 / (M : ℝ)) * ∑ j : Fin M,
    (klDiv (P j) (InfoTheory.mixtureMeasure M P)).toReal ≤
    (1 / (M : ℝ) ^ 2) * ∑ j : Fin M, ∑ k : Fin M,
      (klDiv (P j) (P k)).toReal := by
    have := kl_mixture_le_avg_pairwise M hM P hac hfin
    simp_rw [mixtureMeasure_eq_infoTheory] at this
    exact this
  linarith

end FanoInequality

namespace FanoInequality

/--
[fano_inequality](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/Thm_5_10.lean)
-/
@[path]
lemma fano_inequality
  [MeasurableSpace Ω]
  {M : ℕ}
  {P : Fin M → Measure Ω}
  [∀ j, IsProbabilityMeasure (P j)]
-- given
  (hM : 3 ≤ M)
  (hac : ∀ j k, P j ≪ P k)
  (hfin : ∀ j k, klDiv (P j) (P k) ≠ ⊤) :
-- imply
  ∀ (ψ : Ω → Fin M), Measurable ψ → ∃ j : Fin M, (P j {ω | ψ ω ≠ j}).toReal ≥ 1 - ((1 / (M : ℝ) ^ 2) * ∑ j : Fin M, ∑ k : Fin M, (klDiv (P j) (P k)).toReal + Real.log 2) / Real.log ((M : ℝ) - 1) := by
-- proof
  intro ψ hψ
  obtain ⟨j, hj⟩ := fano_lemma M hM P hac hfin ψ hψ
  refine ⟨j, le_trans ?_ hj⟩
  have hM2 : 2 ≤ M := by omega
  have hkl := kl_mixture_le_avg_pairwise M hM2 P hac hfin
  have hlog : 0 ≤ Real.log ((M : ℝ) - 1) := by
    apply Real.log_nonneg
    have : (2 : ℝ) ≤ (M : ℝ) := Nat.ofNat_le_cast.mpr hM2
    linarith
  have hsums : (1 / (M : ℝ)) * ∑ j : Fin M,
    (klDiv (P j) (mixtureMeasure P)).toReal + Real.log 2 ≤
    (1 / (M : ℝ) ^ 2) * ∑ j : Fin M, ∑ k : Fin M,
      (klDiv (P j) (P k)).toReal + Real.log 2 := by linarith
  linarith [div_le_div_of_nonneg_right hsums hlog]

end FanoInequality


-- created on 2026-10-23
