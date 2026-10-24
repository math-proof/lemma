import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.DifferentialAnalysis.code.OuterMeasureFromFunctional
open Set TopologicalSpace MeasureTheory MeasuresAndSigmaAlgebras
open scoped ENNReal NNReal Topology ZeroAtInfty


namespace MeasuresAndSigmaAlgebras

/--
[functionalMeasureOpen_mono](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/OuterMeasureFromFunctional.lean)
-/
@[path]
lemma functionalMeasureOpen_mono
  [MetricSpace X]
  [LocallyCompactSpace X]
  [MetricSpace X]
  {u : C₀(X, ℝ) →L[ℝ] ℝ}
  ⦃U V : Set X⦄
-- given
  (hU : IsOpen U)
  (hV : IsOpen V)
  (h : U ⊆ V) :
-- imply
  functionalMeasureOpen u U hU ≤ functionalMeasureOpen u V hV := by
-- proof
  apply iSup₂_le
  intro f ⟨hf01, hcomp, hsupp⟩
  exact le_iSup₂_of_le f ⟨hf01, hcomp, hsupp.trans h⟩ le_rfl

end MeasuresAndSigmaAlgebras

namespace MeasuresAndSigmaAlgebras

/--
[functionalOuterMeasure_isOuterMeasure](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/OuterMeasureFromFunctional.lean)
-/
@[path]
lemma functionalOuterMeasure_isOuterMeasure
  [MetricSpace X]
  [LocallyCompactSpace X]
  {u : C₀(X, ℝ) →L[ℝ] ℝ}
-- given
  (hu : IsPositiveLinearFunctional u) :
-- imply
  IsOuterMeasure (⇑(functionalOuterMeasure u hu)) :=
-- proof
  outerMeasure_isOuterMeasure (functionalOuterMeasure u hu)
end MeasuresAndSigmaAlgebras


/--
[zeroAtInfty_eq_zero_of_tsupport_subset_empty](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/OuterMeasureFromFunctional.lean)
-/
@[path]
private lemma zeroAtInfty_eq_zero_of_tsupport_subset_empty_eq
  [MetricSpace X]
  [LocallyCompactSpace X]
  [MetricSpace X]
  {f : C₀(X, ℝ)}
-- given
  (h : tsupport f ⊆ (∅ : Set X)) :
-- imply
  f = 0 := by
-- proof
  apply MeasuresAndSigmaAlgebras.zeroAtInfty_eq_zero_of_tsupport_subset_empty h

/--
[functionalMeasureOpen_empty](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/OuterMeasureFromFunctional.lean)
-/
@[path]
private lemma functionalMeasureOpen_empty_eq
  [MetricSpace X]
  [LocallyCompactSpace X]
  [MetricSpace X]
  {u : C₀(X, ℝ) →L[ℝ] ℝ} :
-- imply
  functionalMeasureOpen u ∅ isOpen_empty = 0 := by
-- proof
  apply MeasuresAndSigmaAlgebras.functionalMeasureOpen_empty u


-- created on 2026-10-23
