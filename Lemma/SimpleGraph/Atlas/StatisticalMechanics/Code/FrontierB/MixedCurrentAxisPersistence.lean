import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierB.MixedCurrentAxisPersistence.Part2
open Filter MeasureTheory Set Topology StatMech StatMech.FrontierB


/--
[independentMixedPairConfigLaw_axisCofinalGenMixing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/MixedCurrentAxisPersistence.lean)
-/
@[path]
private lemma independentMixedPairConfigLaw_axisCofinalGenMixing_eq
  [Countable E]
  [Group H]
  [MulAction H E]
  {axis : Nat → H}
  {rho nu : ProbabilityMeasure (ConfigSpace E)}
-- given
  (hrho : fmu_AxisCofinalGenMixing axis (rho : Measure (ConfigSpace E)))
  (hnu : fmu_AxisEventuallyGenMixing axis (nu : Measure (ConfigSpace E))) :
-- imply
  fmu_AxisCofinalPairMixing axis (independentMixedPairConfigLaw rho nu : Measure (ConfigSpace (E ⊕ E))) := by
-- proof
  apply StatMech.FrontierB.independentMixedPairConfigLaw_axisCofinalGenMixing axis rho nu hrho hnu

/--
[freePlusCurrentTracePairLaw_axisCofinalGenMixing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/MixedCurrentAxisPersistence.lean)
-/
@[path]
private lemma freePlusCurrentTracePairLaw_axisCofinalGenMixing_eq
  [Countable E]
  [Group H]
  [MulAction H E]
  {d : Nat}
  {beta : Real}
-- given
  (hd : 1 ≤ d)
  (hbeta : 0 < beta) :
-- imply
  fmu_AxisCofinalPairMixing (fun k => FK.freeAxisTranslationPower hd k) (independentMixedPairConfigLaw (currentTraceLaw (infiniteFreeCurrentMeasure d beta hbeta.le)) (currentTraceLaw (infinitePlusCurrentMeasure d beta hbeta.le)) : Measure (ConfigSpace (Sym2 (Site d) ⊕ Sym2 (Site d)))) := by
-- proof
  apply StatMech.FrontierB.freePlusCurrentTracePairLaw_axisCofinalGenMixing hd hbeta

/--
[fmu_axisCofinalGenMixing_of_axisCofinalPairMixing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/MixedCurrentAxisPersistence.lean)
-/
@[path]
private lemma fmu_axisCofinalGenMixing_of_axisCofinalPairMixing_eq
  [Countable E]
  [Group H]
  [MulAction H E]
  {rho : Measure (ConfigSpace E)}
  [IsProbabilityMeasure rho]
  {axis : Nat → H}
-- given
  (hmix : fmu_AxisCofinalPairMixing axis rho) :
-- imply
  fmu_AxisCofinalGenMixing axis rho := by
-- proof
  apply StatMech.FrontierB.fmu_axisCofinalGenMixing_of_axisCofinalPairMixing axis hmix

/--
[freePlusCurrentTracePairLaw_axisCofinalGenMixing_full](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/MixedCurrentAxisPersistence.lean)
-/
@[path]
private lemma freePlusCurrentTracePairLaw_axisCofinalGenMixing_full_eq
  [Countable E]
  [Group H]
  [MulAction H E]
  {d : Nat}
  {beta : Real}
-- given
  (hd : 1 ≤ d)
  (hbeta : 0 < beta) :
-- imply
  fmu_AxisCofinalGenMixing (fun k => FK.freeAxisTranslationPower hd k) (independentMixedPairConfigLaw (currentTraceLaw (infiniteFreeCurrentMeasure d beta hbeta.le)) (currentTraceLaw (infinitePlusCurrentMeasure d beta hbeta.le)) : Measure (ConfigSpace (Sym2 (Site d) ⊕ Sym2 (Site d)))) := by
-- proof
  apply StatMech.FrontierB.freePlusCurrentTracePairLaw_axisCofinalGenMixing_full hd hbeta

/--
[independentMixedOrConfigLaw_axisCofinalGenMixing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/MixedCurrentAxisPersistence.lean)
-/
@[path]
private lemma independentMixedOrConfigLaw_axisCofinalGenMixing_eq
  [Countable E]
  [Group H]
  [MulAction H E]
  {axis : Nat → H}
  {rho nu : ProbabilityMeasure (ConfigSpace E)}
-- given
  (hmix : fmu_AxisCofinalGenMixing axis (independentMixedPairConfigLaw rho nu : Measure (ConfigSpace (E ⊕ E)))) :
-- imply
  fmu_AxisCofinalGenMixing axis (independentMixedOrConfigLaw rho nu : Measure (ConfigSpace E)) := by
-- proof
  apply StatMech.FrontierB.independentMixedOrConfigLaw_axisCofinalGenMixing axis rho nu hmix

/--
[freePlusSuperposedTraceLaw_axisCofinalGenMixing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/MixedCurrentAxisPersistence.lean)
-/
@[path]
private lemma freePlusSuperposedTraceLaw_axisCofinalGenMixing_eq
  [Countable E]
  [Group H]
  [MulAction H E]
  {d : Nat}
  {beta : Real}
-- given
  (hd : 1 ≤ d)
  (hbeta : 0 < beta) :
-- imply
  fmu_AxisCofinalGenMixing (fun k => FK.freeAxisTranslationPower hd k) (independentSuperposedTraceLaw (infiniteFreeCurrentMeasure d beta hbeta.le) (infinitePlusCurrentMeasure d beta hbeta.le) : Measure (ConfigSpace (Sym2 (Site d)))) := by
-- proof
  apply StatMech.FrontierB.freePlusSuperposedTraceLaw_axisCofinalGenMixing hd hbeta

/--
[fmu_axisCofinal_event_exists_after](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/MixedCurrentAxisPersistence.lean)
-/
@[path]
private lemma fmu_axisCofinal_event_exists_after_eq
  [Countable E]
  [Group H]
  [MulAction H E]
  {rho : Measure (ConfigSpace E)}
  [IsProbabilityMeasure rho]
  {axis : Nat → H}
  {s : Set (ConfigSpace E)}
  {K : Nat}
  {epsilon : Real}
-- given
  (hti : IsTranslationInvariant (G := H) rho)
  (hmix : fmu_AxisCofinalGenMixing axis rho)
  (hs : MeasurableSet s)
  (hepsilon : 0 < epsilon) :
-- imply
  ∃ k : Nat, K ≤ k ∧ abs (rho.real (s ∩ (shift (axis k) : ConfigSpace E → ConfigSpace E) ⁻¹' s) - (rho.real s) ^ 2) < 5 * epsilon := by
-- proof
  apply StatMech.FrontierB.fmu_axisCofinal_event_exists_after axis hti hmix s hs K epsilon hepsilon

/--
[currentContinuityAxisPercolationPrinciple_of_mixing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/MixedCurrentAxisPersistence.lean)
-/
@[path]
private lemma currentContinuityAxisPercolationPrinciple_of_mixing_eq
  [Countable E]
  [Group H]
  [MulAction H E]
  {d : Nat}
  {rho : ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))}
-- given
  (hd : 1 ≤ d)
  (hti : IsTranslationInvariant (G := Multiplicative (Site d)) (rho : Measure (ConfigSpace (Sym2 (Site d)))))
  (hmix : fmu_AxisCofinalGenMixing (fun k => FK.freeAxisTranslationPower hd k) (rho : Measure (ConfigSpace (Sym2 (Site d)))))
  (hunique : (rho : Measure (ConfigSpace (Sym2 (Site d)))) (atLeastTwoInfinite d) = 0) :
-- imply
  CurrentContinuityAxisPercolationPrinciple d hd (rho : Measure (ConfigSpace (Sym2 (Site d)))) := by
-- proof
  apply StatMech.FrontierB.currentContinuityAxisPercolationPrinciple_of_mixing d hd rho hti hmix hunique

/--
[currentContinuityMixedTraceLaw_axisPercolationPrinciple](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/MixedCurrentAxisPersistence.lean)
-/
@[path]
private lemma currentContinuityMixedTraceLaw_axisPercolationPrinciple_eq
  [Countable E]
  [Group H]
  [MulAction H E]
  {d : Nat}
  {beta : Real}
-- given
  (hd : 1 ≤ d)
  (hbeta : 0 < beta) :
-- imply
  CurrentContinuityAxisPercolationPrinciple d hd (currentContinuityMixedTraceLaw d beta hbeta : Measure _) := by
-- proof
  apply StatMech.FrontierB.currentContinuityMixedTraceLaw_axisPercolationPrinciple d hd beta hbeta

/--
[currentContinuity_no_axis_persistent_connectivity_of_freeAxisLROZero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/MixedCurrentAxisPersistence.lean)
-/
@[path]
private lemma currentContinuity_no_axis_persistent_connectivity_of_freeAxisLROZero_eq
  [Countable E]
  [Group H]
  [MulAction H E]
  {d : Nat}
  {beta : Real}
-- given
  (hd : 1 ≤ d)
  (hbeta : 0 < beta)
  (hunique : (currentContinuityMixedTraceLaw d beta hbeta : Measure _) (atLeastTwoInfinite d) = 0)
  (hLRO : CurrentContinuityFreeAxisLROZero d hd beta) :
-- imply
  ¬ CurrentContinuityAxisConnectivityPersists d hd (currentContinuityMixedTraceLaw d beta hbeta : Measure _) := by
-- proof
  apply StatMech.FrontierB.currentContinuity_no_axis_persistent_connectivity_of_freeAxisLROZero hd beta hbeta hunique hLRO

/--
[currentContinuity_no_percolation_of_freeAxisLROZero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/MixedCurrentAxisPersistence.lean)
-/
@[path]
private lemma currentContinuity_no_percolation_of_freeAxisLROZero_eq
  [Countable E]
  [Group H]
  [MulAction H E]
  {d : Nat}
  {beta : Real}
-- given
  (hd : 1 ≤ d)
  (hbeta : 0 < beta)
  (hLRO : CurrentContinuityFreeAxisLROZero d hd beta) :
-- imply
  (currentContinuityMixedTraceLaw d beta hbeta : Measure _).real (percolationEvent d) = 0 := by
-- proof
  apply StatMech.FrontierB.currentContinuity_no_percolation_of_freeAxisLROZero hd beta hbeta hLRO


-- created on 2026-10-23
