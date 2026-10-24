import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.DifferentialAnalysis.code.MeasuresAndSigmaAlgebras
open MeasureTheory Set MeasuresAndSigmaAlgebras
open scoped ENNReal
open scoped NNReal
open CompactlySupportedContinuousMap
open Measure RealRMK
open scoped CompactlySupported ZeroAtInfty


namespace MeasuresAndSigmaAlgebras

/--
[outerMeasure_isOuterMeasure](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/MeasuresAndSigmaAlgebras.lean)
-/
@[path]
lemma outerMeasure_isOuterMeasure
  {μ : OuterMeasure X} :
-- imply
  IsOuterMeasure (⇑μ) where empty :=
-- proof
  measure_empty
    mono h := measure_mono h
    iUnion_le A := measure_iUnion_le A

end MeasuresAndSigmaAlgebras

namespace MeasuresAndSigmaAlgebras

/--
[lebesgue_borel_le_caratheodory](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/MeasuresAndSigmaAlgebras.lean)
-/
@[path]
lemma lebesgue_borel_le_caratheodory
  {n : ℕ} :
-- imply
  borel (Fin n → ℝ) ≤ (volume : Measure (Fin n → ℝ)).toOuterMeasure.caratheodory :=
-- proof
  le_trans OpensMeasurableSpace.borel_le (le_toOuterMeasure_caratheodory volume)

end MeasuresAndSigmaAlgebras

namespace MeasuresAndSigmaAlgebras

/--
[isOuterMeasureMeasurable_iff_isCaratheodory](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/MeasuresAndSigmaAlgebras.lean)
-/
@[path]
lemma isOuterMeasureMeasurable_iff_isCaratheodory
  {μ : OuterMeasure X}
  {E : Set X} :
-- imply
  IsOuterMeasureMeasurable (⇑μ) E ↔ μ.IsCaratheodory E := by
-- proof
  simp only [IsOuterMeasureMeasurable, OuterMeasure.IsCaratheodory, sdiff_eq, Set.inf_eq_inter]
section CaratheodoryMeasurable
variable {X : Type*} (μ : OuterMeasure X)
/-- The σ-algebra of Carathéodory-measurable sets for an outer measure `μ`. -/
@[reducible] def caratheodorySigmaAlgebra : SigmaAlgebra X := μ.caratheodory
end CaratheodoryMeasurable
section Caratheodory

end MeasuresAndSigmaAlgebras

namespace MeasuresAndSigmaAlgebras

/--
[isOuterMeasureMeasurable_of_measure_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/MeasuresAndSigmaAlgebras.lean)
-/
@[path]
lemma isOuterMeasureMeasurable_of_measure_zero
  {μ : OuterMeasure X}
  {E : Set X}
-- given
  (hE : μ E = 0) :
-- imply
  μ.IsCaratheodory E := by
-- proof
  rw [OuterMeasure.isCaratheodory_iff_le']
  intro A
  have hAE : μ (A ∩ E) = 0 :=
    le_antisymm ((measure_mono Set.inter_subset_right).trans hE.le) (zero_le _)
  have hAEc : μ (A \ E) ≤ μ A := measure_mono diff_subset
  rwa [hAE, zero_add]

end MeasuresAndSigmaAlgebras

namespace MeasuresAndSigmaAlgebras

/--
[caratheodoryMeasure_isComplete](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/MeasuresAndSigmaAlgebras.lean)
-/
@[path]
lemma caratheodoryMeasure_isComplete
  {μ : OuterMeasure X} :
-- imply
  @Measure.IsComplete X μ.caratheodory (caratheodoryMeasure μ) := by
-- proof
  letI : MeasurableSpace X := μ.caratheodory
  constructor
  intro s hs
  have hμs : μ s = 0 := by
    have h1 : μ s ≤ (caratheodoryMeasure μ) s := le_toMeasure_apply μ le_rfl s
    rw [hs] at h1
    exact le_antisymm h1 (zero_le _)
  exact isOuterMeasureMeasurable_of_measure_zero μ hμs

end MeasuresAndSigmaAlgebras

namespace MeasuresAndSigmaAlgebras

/--
[caratheodory_theorem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/MeasuresAndSigmaAlgebras.lean)
-/
@[path]
lemma caratheodory_theorem
  {μ : OuterMeasure X} :
-- imply
  ∃ (m : @Measure X μ.caratheodory), @Measure.IsComplete X μ.caratheodory m ∧ (∀ (s : Set X), MeasurableSet[μ.caratheodory] s → m s = μ s) := by
-- proof
  letI : MeasurableSpace X := μ.caratheodory
  exact ⟨caratheodoryMeasure μ,
    caratheodoryMeasure_isComplete μ,
    fun s hs => toMeasure_apply μ le_rfl hs⟩
section RieszOuterMeasureMeasurability
open scoped NNReal
open CompactlySupportedContinuousMap

end MeasuresAndSigmaAlgebras

namespace MeasuresAndSigmaAlgebras

/--
[isOpen_outerMeasureMeasurable_and_measure_eq_innerContent](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/MeasuresAndSigmaAlgebras.lean)
-/
@[path]
lemma isOpen_outerMeasureMeasurable_and_measure_eq_innerContent
  [MetricSpace X]
  [LocallyCompactSpace X]
  {Λ : CompactlySupportedContinuousMap X ℝ →ₚ[ℝ] ℝ}
  [MeasurableSpace X]
  [BorelSpace X]
  {U : Set X}
-- given
  (hU : IsOpen U) :
-- imply
  IsOuterMeasureMeasurable (⇑(rieszContent (toNNRealLinear Λ)).outerMeasure) U ∧ (rieszContent (toNNRealLinear Λ)).measure U = (rieszContent (toNNRealLinear Λ)).innerContent ⟨U, hU⟩ := by
-- proof
  constructor
  · intro A
    exact (rieszContent (toNNRealLinear Λ)).borel_le_caratheodory U hU.measurableSet A
  · rw [(rieszContent (toNNRealLinear Λ)).measure_apply hU.measurableSet]
    exact (rieszContent (toNNRealLinear Λ)).outerMeasure_of_isOpen U hU
section RieszMeasureRadon
open Measure RealRMK
variable {X : Type*} [TopologicalSpace X] [T2Space X] [MeasurableSpace X]
  [BorelSpace X] [LocallyCompactSpace X]
  (Λ : CompactlySupportedContinuousMap X ℝ →ₚ[ℝ] ℝ)

end MeasuresAndSigmaAlgebras

namespace MeasuresAndSigmaAlgebras

/--
[prop_2_8_radon_measure_from_C0_functional](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/MeasuresAndSigmaAlgebras.lean)
-/
@[path]
lemma prop_2_8_radon_measure_from_C0_functional
  [TopologicalSpace X]
  [T2Space X]
  [MeasurableSpace X]
  {Φ : C₀(X, ℝ) →ₗ[ℝ] ℝ}
-- given
  (hΦ : ∀ f : C₀(X, ℝ), (∀ x, 0 ≤ f x) → 0 ≤ Φ f) :
-- imply
  IsRadonMeasure (rieszMeasureOfC0Functional Φ hΦ) := by
-- proof
  show IsRadonMeasure (rieszMeasure _)
  exact ⟨⟩

end MeasuresAndSigmaAlgebras

namespace MeasuresAndSigmaAlgebras

/--
[borel_le_caratheodory_of_openSets_measurable](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/MeasuresAndSigmaAlgebras.lean)
-/
@[path]
lemma borel_le_caratheodory_of_openSets_measurable
  [TopologicalSpace X]
  {μ : OuterMeasure X}
-- given
  (h : ∀ (U : Set X), IsOpen U → IsOuterMeasureMeasurable (⇑μ) U) :
-- imply
  borel X ≤ μ.caratheodory :=
-- proof
  MeasurableSpace.generateFrom_le fun U hU =>
    (isOuterMeasureMeasurable_iff_isCaratheodory μ U).mp (h U hU)

end MeasuresAndSigmaAlgebras


-- created on 2026-10-23
