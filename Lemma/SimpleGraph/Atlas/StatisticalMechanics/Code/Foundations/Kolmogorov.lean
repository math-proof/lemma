import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Foundations.Kolmogorov.Part2
open MeasureTheory StatMech StatMech.Kolmogorov


/--
[extension_isProbabilityMeasure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/Kolmogorov.lean)
-/
@[path]
private lemma extension_isProbabilityMeasure_eq
  {X : ι → Type*}
  [∀ i, MeasurableSpace (X i)] :
-- imply
  IsProbabilityMeasure (extension μ) := by
-- proof
  apply StatMech.Kolmogorov.extension_isProbabilityMeasure

/--
[extension_isProjectiveLimit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/Kolmogorov.lean)
-/
@[path]
private lemma extension_isProjectiveLimit_eq
  {X : ι → Type*}
  [∀ i, MeasurableSpace (X i)] :
-- imply
  IsProjectiveLimit (extension μ) (fun I : Finset ι => Measure.pi (fun i : I => μ i)) := by
-- proof
  apply StatMech.Kolmogorov.extension_isProjectiveLimit

/--
[extension_map_restrict](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/Kolmogorov.lean)
-/
@[path]
private lemma extension_map_restrict_eq
  {X : ι → Type*}
  [∀ i, MeasurableSpace (X i)]
  {I : Finset ι} :
-- imply
  (extension μ).map I.restrict = Measure.pi (fun i : I => μ i) := by
-- proof
  apply StatMech.Kolmogorov.extension_map_restrict I

/--
[extension_cylinder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/Kolmogorov.lean)
-/
@[path]
private lemma extension_cylinder_eq
  {X : ι → Type*}
  [∀ i, MeasurableSpace (X i)]
  {I : Finset ι}
  {S : Set (Π i : I, X i)}
-- given
  (hS : MeasurableSet S) :
-- imply
  extension μ (cylinder I S) = Measure.pi (fun i : I => μ i) S := by
-- proof
  apply StatMech.Kolmogorov.extension_cylinder hS

/--
[extension_pi](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/Kolmogorov.lean)
-/
@[path]
private lemma extension_pi_eq
  {X : ι → Type*}
  [∀ i, MeasurableSpace (X i)]
  {s : Finset ι}
  {t : (i : ι) → Set (X i)}
-- given
  (ht : ∀ i ∈ s, MeasurableSet (t i)) :
-- imply
  extension μ (Set.pi s t) = ∏ i ∈ s, μ i (t i) := by
-- proof
  apply StatMech.Kolmogorov.extension_pi ht

/--
[extension_unique](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/Kolmogorov.lean)
-/
@[path]
private lemma extension_unique_eq
  {X : ι → Type*}
  [∀ i, MeasurableSpace (X i)]
  {ν : Measure (Π i, X i)}
-- given
  (hν : ∀ (s : Finset ι) (t : (i : ι) → Set (X i)), (∀ i, MeasurableSet (t i)) → ν (Set.pi s t) = ∏ i ∈ s, μ i (t i)) :
-- imply
  ν = extension μ := by
-- proof
  apply StatMech.Kolmogorov.extension_unique hν

/--
[extension_unique_of_isProjectiveLimit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/Kolmogorov.lean)
-/
@[path]
private lemma extension_unique_of_isProjectiveLimit_eq
  {X : ι → Type*}
  [∀ i, MeasurableSpace (X i)]
  {ν : Measure (Π i, X i)}
-- given
  (hν : IsProjectiveLimit ν (fun I : Finset ι => Measure.pi (fun i : I => μ i))) :
-- imply
  ν = extension μ := by
-- proof
  apply StatMech.Kolmogorov.extension_unique_of_isProjectiveLimit hν

/--
[configExtension_isProjectiveLimit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/Kolmogorov.lean)
-/
@[path]
private lemma configExtension_isProjectiveLimit_eq
  {μ : E → Measure Bool}
  [∀ e, IsProbabilityMeasure (μ e)] :
-- imply
  IsProjectiveLimit (configExtension μ) (fun I : Finset E => Measure.pi (fun e : I => μ e)) := by
-- proof
  apply StatMech.Kolmogorov.configExtension_isProjectiveLimit μ

/--
[configExtension_unique](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/Kolmogorov.lean)
-/
@[path]
private lemma configExtension_unique_eq
  {μ : E → Measure Bool}
  [∀ e, IsProbabilityMeasure (μ e)]
  {ν : Measure (ConfigSpace E)}
-- given
  (hν : ∀ (s : Finset E) (t : E → Set Bool), (∀ e, MeasurableSet (t e)) → ν (Set.pi s t) = ∏ e ∈ s, μ e (t e)) :
-- imply
  ν = configExtension μ := by
-- proof
  apply StatMech.Kolmogorov.configExtension_unique μ hν


-- created on 2026-10-23
