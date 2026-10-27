import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.FiniteEventMultivalued
open MeasureTheory Set Finset StatMech StatMech.FrontierA


/--
[finiteEventMultiplicity_eq_sum_indicator](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FiniteEventMultivalued.lean)
-/
@[path]
private lemma finiteEventMultiplicity_eq_sum_indicator_eq
  [MeasurableSpace Omega]
  {J : Finset I}
  {A : I → Set Omega}
  {omega : Omega} :
-- imply
  (finiteEventMultiplicity J A omega : ℝ≥0∞) = ∑ i ∈ J, (A i).indicator (fun _ => (1 : ℝ≥0∞)) omega := by
-- proof
  apply StatMech.FrontierA.finiteEventMultiplicity_eq_sum_indicator J A omega

/--
[lintegral_finiteEventMultiplicity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FiniteEventMultivalued.lean)
-/
@[path]
private lemma lintegral_finiteEventMultiplicity_eq
  [MeasurableSpace Omega]
  {mu : Measure Omega}
  {J : Finset I}
  {A : I → Set Omega}
-- given
  (hA : ∀ i ∈ J, MeasurableSet (A i)) :
-- imply
  ∫⁻ omega, (finiteEventMultiplicity J A omega : ℝ≥0∞) ∂mu = ∑ i ∈ J, mu (A i) := by
-- proof
  apply StatMech.FrontierA.lintegral_finiteEventMultiplicity mu J A hA

/--
[finiteEventMultivalued_probability_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FiniteEventMultivalued.lean)
-/
@[path]
private lemma finiteEventMultivalued_probability_bound_eq
  [MeasurableSpace Omega]
  {mu : Measure Omega}
  [IsProbabilityMeasure mu]
  {J : Finset I}
  {source target : I → Set Omega}
  {E : Set Omega}
  {K L : Nat}
-- given
  (hsourceMeas : ∀ i ∈ J, MeasurableSet (source i))
  (htargetMeas : ∀ i ∈ J, MeasurableSet (target i))
  (hEMeas : MeasurableSet E)
  (c : ℝ≥0∞)
  (hsourceDegree : ∀ omega ∈ E, K ≤ finiteEventMultiplicity J source omega)
  (htargetDegree : ∀ omega, finiteEventMultiplicity J target omega ≤ L)
  (htransfer : ∀ i ∈ J, c * mu (source i) ≤ mu (target i)) :
-- imply
  c * K * mu E ≤ L := by
-- proof
  apply StatMech.FrontierA.finiteEventMultivalued_probability_bound mu J source target hsourceMeas htargetMeas E hEMeas c K L hsourceDegree htargetDegree htransfer


-- created on 2026-10-23
