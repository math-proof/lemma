import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FK.PairMixingGenMixing
open MeasureTheory Set StatMech StatMech.FK


/--
[fmu_real_inter_shift_eq_cross_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PairMixingGenMixing.lean)
-/
@[path]
private lemma fmu_real_inter_shift_eq_cross_sum_eq
  [Group G]
  [MulAction G E]
  {mu : Measure (ConfigSpace E)}
  [Countable E]
  [IsProbabilityMeasure mu]
  {g : G}
  {A B : Set (ConfigSpace E)}
  {P Q : Finset (Finset E)}
-- given
  (hA : MeasurableSet A)
  (hB : MeasurableSet B)
  (c e : Finset E -> Real)
  (hAexp : forall omega, A.indicator (fun _ => (1 : Real)) omega = ∑ T ∈ P, c T * fmu_moInd T omega)
  (hBexp : forall omega, B.indicator (fun _ => (1 : Real)) omega = ∑ U ∈ Q, e U * fmu_moInd U omega) :
-- imply
  mu.real (A ∩ (shift g) ⁻¹' B) = ∑ T ∈ P, ∑ U ∈ Q, c T * e U * mu.real (fmu_multiOpen T ∩ (shift g : ConfigSpace E -> ConfigSpace E) ⁻¹' fmu_multiOpen U) := by
-- proof
  apply StatMech.FK.fmu_real_inter_shift_eq_cross_sum g hA hB P Q c e hAexp hBexp

/--
[fmu_genMixing_of_pairMixing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PairMixingGenMixing.lean)
-/
@[path]
private lemma fmu_genMixing_of_pairMixing_eq
  [Group G]
  [MulAction G E]
  {mu : Measure (ConfigSpace E)}
  [Countable E]
  [IsProbabilityMeasure mu]
-- given
  (hmix : fmu_PairMixing (G := G) mu) :
-- imply
  fmu_GenMixing (G := G) mu := by
-- proof
  apply StatMech.FK.fmu_genMixing_of_pairMixing hmix


-- created on 2026-10-23
