import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.BernoulliGlobalFKG.Part2
open MeasureTheory Set Filter StatMech StatMech.Universality


/--
[bernoulli_finiteCylinderPositivelyAssociated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BernoulliGlobalFKG.lean)
-/
@[path]
private lemma bernoulli_finiteCylinderPositivelyAssociated_eq
  [Countable E]
-- given
  (p : NNReal)
  (hp : p ≤ 1) :
-- imply
  FiniteCylinderPositivelyAssociated (bernoulliProductMeasure (E := E) p hp) := by
-- proof
  apply StatMech.Universality.bernoulli_finiteCylinderPositivelyAssociated p hp

/--
[rba_selfDualMeasure_finiteCylinderPositivelyAssociated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BernoulliGlobalFKG.lean)
-/
@[path]
private lemma rba_selfDualMeasure_finiteCylinderPositivelyAssociated_eq :
-- imply
  FiniteCylinderPositivelyAssociated rba_selfDualMeasure := by
-- proof
  apply StatMech.Universality.rba_selfDualMeasure_finiteCylinderPositivelyAssociated

/--
[FiniteCylinderPositivelyAssociated.triple](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BernoulliGlobalFKG.lean)
-/
@[path]
private lemma triple_eq
  {μ : Measure (ConfigSpace E)}
  {A B C : Set (ConfigSpace E)}
  {F G K : Finset E}
-- given
  (hpa : FiniteCylinderPositivelyAssociated μ)
  (hA : IsIncreasing A)
  (hB : IsIncreasing B)
  (hC : IsIncreasing C)
  (hAF : _root_.DependsOn (A.indicator (fun _ => (1 : ℝ))) (F : Set E))
  (hBG : _root_.DependsOn (B.indicator (fun _ => (1 : ℝ))) (G : Set E))
  (hCK : _root_.DependsOn (C.indicator (fun _ => (1 : ℝ))) (K : Set E)) :
-- imply
  μ.real A * μ.real B * μ.real C ≤ μ.real (A ∩ B ∩ C) := by
-- proof
  apply StatMech.Universality.FiniteCylinderPositivelyAssociated.triple hpa hA hB hC F G K hAF hBG hCK

/--
[rba_horizontal_strip_glue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BernoulliGlobalFKG.lean)
-/
@[path]
private lemma rba_horizontal_strip_glue_eq
  {a m m' b c d : ℤ}
-- given
  (ham : a ≤ m)
  (hmm' : m ≤ m')
  (hm'b : m' ≤ b)
  (hamL : a < m')
  (hmbR : m < b)
  (hcd : c ≤ d) :
-- imply
  rba_selfDualMeasure.real (horizontalCrossingEvent a m' c d) * rba_selfDualMeasure.real (verticalCrossingEvent m m' c d) * rba_selfDualMeasure.real (horizontalCrossingEvent m b c d) ≤ rba_selfDualMeasure.real (horizontalCrossingEvent a b c d) := by
-- proof
  apply StatMech.Universality.rba_horizontal_strip_glue ham hmm' hm'b hamL hmbR hcd

/--
[rba_vertical_strip_glue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BernoulliGlobalFKG.lean)
-/
@[path]
private lemma rba_vertical_strip_glue_eq
  {a b c m m' d : ℤ}
-- given
  (hab : a ≤ b)
  (hcm : c ≤ m)
  (hmm' : m ≤ m')
  (hm'd : m' ≤ d)
  (hcm' : c < m')
  (hmd : m < d) :
-- imply
  rba_selfDualMeasure.real (verticalCrossingEvent a b c m') * rba_selfDualMeasure.real (horizontalCrossingEvent a b m m') * rba_selfDualMeasure.real (verticalCrossingEvent a b m d) ≤ rba_selfDualMeasure.real (verticalCrossingEvent a b c d) := by
-- proof
  apply StatMech.Universality.rba_vertical_strip_glue hab hcm hmm' hm'd hcm' hmd

/--
[measurablyPositivelyAssociated_of_increasingCylinderApproximation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BernoulliGlobalFKG.lean)
-/
@[path]
private lemma measurablyPositivelyAssociated_of_increasingCylinderApproximation_eq
  {μ : Measure (ConfigSpace E)}
  [IsFiniteMeasure μ]
-- given
  (hcyl : FiniteCylinderPositivelyAssociated μ)
  (happrox : ∀ A : Set (ConfigSpace E), MeasurableSet A → IsIncreasing A → HasIncreasingCylinderApproximation μ A) :
-- imply
  MeasurablyPositivelyAssociated μ := by
-- proof
  apply StatMech.Universality.measurablyPositivelyAssociated_of_increasingCylinderApproximation hcyl happrox

/--
[positivelyAssociated_of_measurablyPositivelyAssociated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BernoulliGlobalFKG.lean)
-/
@[path]
private lemma positivelyAssociated_of_measurablyPositivelyAssociated_eq
  {μ : Measure (ConfigSpace E)}
-- given
  (hpa : MeasurablyPositivelyAssociated μ)
  (hmeas : ∀ A : Set (ConfigSpace E), IsIncreasing A → MeasurableSet A) :
-- imply
  PositivelyAssociated μ := by
-- proof
  apply StatMech.Universality.positivelyAssociated_of_measurablyPositivelyAssociated hpa hmeas

/--
[bernoulli_exists_cylinder_symmDiff_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BernoulliGlobalFKG.lean)
-/
@[path]
private lemma bernoulli_exists_cylinder_symmDiff_lt_eq
  [Countable E]
  {A : Set (ConfigSpace E)}
  {ε : ENNReal}
-- given
  (p : NNReal)
  (hp : p ≤ 1)
  (hA : MeasurableSet A)
  (hε : 0 < ε) :
-- imply
  ∃ C ∈ measurableCylinders (fun _ : E => Bool), bernoulliProductMeasure (E := E) p hp (C ∆ A) < ε := by
-- proof
  apply StatMech.Universality.bernoulli_exists_cylinder_symmDiff_lt p hp hA hε


-- created on 2026-10-23
