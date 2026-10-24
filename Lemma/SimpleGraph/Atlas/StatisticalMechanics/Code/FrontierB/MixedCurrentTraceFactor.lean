import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierB.MixedCurrentTraceFactor
open MeasureTheory Set StatMech StatMech.FrontierB


/--
[pairOrConfig_preimage_cylinder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/MixedCurrentTraceFactor.lean)
-/
@[path]
private lemma pairOrConfig_preimage_cylinder_eq
  [Countable E]
  [Group H]
  [MulAction H E]
  [DecidableEq E]
  {S : Finset E}
-- given
  (A : Set (↑S -> Bool)) :
-- imply
  pairOrConfig ⁻¹' MeasureTheory.cylinder S A = MeasureTheory.cylinder (pairOrSupport S) (pairOrPullbackPatternSet S A) := by
-- proof
  apply StatMech.FrontierB.pairOrConfig_preimage_cylinder S A

/--
[pairOrConfig_preimage_mem_measurableCylinders](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/MixedCurrentTraceFactor.lean)
-/
@[path]
private lemma pairOrConfig_preimage_mem_measurableCylinders_eq
  [Countable E]
  [Group H]
  [MulAction H E]
  {C : Set (ConfigSpace E)}
-- given
  (hC : C ∈ measurableCylinders (fun _ : E => Bool)) :
-- imply
  pairOrConfig ⁻¹' C ∈ measurableCylinders (fun _ : E ⊕ E => Bool) := by
-- proof
  apply StatMech.FrontierB.pairOrConfig_preimage_mem_measurableCylinders hC

/--
[mixedPairOrConfig_measurePreserving](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/MixedCurrentTraceFactor.lean)
-/
@[path]
private lemma mixedPairOrConfig_measurePreserving_eq
  [Countable E]
  [Group H]
  [MulAction H E]
  {rho nu : ProbabilityMeasure (ConfigSpace E)} :
-- imply
  MeasurePreserving pairOrConfig (independentMixedPairConfigLaw rho nu : Measure (ConfigSpace (E ⊕ E))) (independentMixedOrConfigLaw rho nu : Measure (ConfigSpace E)) := by
-- proof
  apply StatMech.FrontierB.mixedPairOrConfig_measurePreserving rho nu

/--
[independentMixedOrConfigLaw_real](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/MixedCurrentTraceFactor.lean)
-/
@[path]
private lemma independentMixedOrConfigLaw_real_eq
  [Countable E]
  [Group H]
  [MulAction H E]
  {rho nu : ProbabilityMeasure (ConfigSpace E)}
  {A : Set (ConfigSpace E)}
-- given
  (hA : MeasurableSet A) :
-- imply
  (independentMixedOrConfigLaw rho nu : Measure (ConfigSpace E)).real A = (independentMixedPairConfigLaw rho nu : Measure (ConfigSpace (E ⊕ E))).real (pairOrConfig ⁻¹' A) := by
-- proof
  apply StatMech.FrontierB.independentMixedOrConfigLaw_real rho nu hA

/--
[pairOrConfig_preimage_inter_shift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/MixedCurrentTraceFactor.lean)
-/
@[path]
private lemma pairOrConfig_preimage_inter_shift_eq
  [Countable E]
  [Group H]
  [MulAction H E]
  {g : H}
  {A B : Set (ConfigSpace E)} :
-- imply
  pairOrConfig ⁻¹' (A ∩ (shift g) ⁻¹' B) = (pairOrConfig ⁻¹' A) ∩ (shift g) ⁻¹' (pairOrConfig ⁻¹' B) := by
-- proof
  apply StatMech.FrontierB.pairOrConfig_preimage_inter_shift g A B

/--
[independentMixedOrConfigLaw_genMixing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/MixedCurrentTraceFactor.lean)
-/
@[path]
private lemma independentMixedOrConfigLaw_genMixing_eq
  [Countable E]
  [Group H]
  [MulAction H E]
  {rho nu : ProbabilityMeasure (ConfigSpace E)}
-- given
  (hmix : fmu_GenMixing (G := H) (independentMixedPairConfigLaw rho nu : Measure (ConfigSpace (E ⊕ E)))) :
-- imply
  fmu_GenMixing (G := H) (independentMixedOrConfigLaw rho nu : Measure (ConfigSpace E)) := by
-- proof
  apply StatMech.FrontierB.independentMixedOrConfigLaw_genMixing rho nu hmix

/--
[independentMixedOrConfigLaw_isTranslationInvariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/MixedCurrentTraceFactor.lean)
-/
@[path]
private lemma independentMixedOrConfigLaw_isTranslationInvariant_eq
  [Countable E]
  [Group H]
  [MulAction H E]
  {rho nu : ProbabilityMeasure (ConfigSpace E)}
-- given
  (hti : IsTranslationInvariant (G := H) (independentMixedPairConfigLaw rho nu : Measure (ConfigSpace (E ⊕ E)))) :
-- imply
  IsTranslationInvariant (G := H) (independentMixedOrConfigLaw rho nu : Measure (ConfigSpace E)) := by
-- proof
  apply StatMech.FrontierB.independentMixedOrConfigLaw_isTranslationInvariant rho nu hti

/--
[independentMixedOr_currentTraceLaw_eq_superposed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/MixedCurrentTraceFactor.lean)
-/
@[path]
private lemma independentMixedOr_currentTraceLaw_eq_superposed_eq
  [Countable E]
  [Group H]
  [MulAction H E]
  {mu nu : ProbabilityMeasure (InfiniteCurrentConfig E)} :
-- imply
  (independentMixedOrConfigLaw (currentTraceLaw mu) (currentTraceLaw nu) : Measure (ConfigSpace E)) = (independentSuperposedTraceLaw mu nu : Measure (ConfigSpace E)) := by
-- proof
  apply StatMech.FrontierB.independentMixedOr_currentTraceLaw_eq_superposed mu nu

/--
[freePlusSuperposedTraceLaw_genMixing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/MixedCurrentTraceFactor.lean)
-/
@[path]
private lemma freePlusSuperposedTraceLaw_genMixing_eq
  [Countable E]
  [Group H]
  [MulAction H E]
  {d : Nat}
  {beta : Real}
-- given
  (hd : 1 ≤ d)
  (hbeta : 0 < beta) :
-- imply
  fmu_GenMixing (G := Multiplicative (Site d)) (independentSuperposedTraceLaw (infiniteFreeCurrentMeasure d beta hbeta.le) (infinitePlusCurrentMeasure d beta hbeta.le) : Measure (ConfigSpace (Sym2 (Site d)))) := by
-- proof
  apply StatMech.FrontierB.freePlusSuperposedTraceLaw_genMixing hd hbeta

/--
[freePlusSuperposedTraceLaw_isTranslationInvariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/MixedCurrentTraceFactor.lean)
-/
@[path]
private lemma freePlusSuperposedTraceLaw_isTranslationInvariant_eq
  [Countable E]
  [Group H]
  [MulAction H E]
  {d : Nat}
  {beta : Real}
-- given
  (hbeta : 0 < beta) :
-- imply
  IsTranslationInvariant (G := Multiplicative (Site d)) (independentSuperposedTraceLaw (infiniteFreeCurrentMeasure d beta hbeta.le) (infinitePlusCurrentMeasure d beta hbeta.le) : Measure (ConfigSpace (Sym2 (Site d)))) := by
-- proof
  apply StatMech.FrontierB.freePlusSuperposedTraceLaw_isTranslationInvariant hbeta

/--
[freePlusSuperposedTraceLaw_isErgodic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/MixedCurrentTraceFactor.lean)
-/
@[path]
private lemma freePlusSuperposedTraceLaw_isErgodic_eq
  [Countable E]
  [Group H]
  [MulAction H E]
  {d : Nat}
  {beta : Real}
-- given
  (hd : 1 ≤ d)
  (hbeta : 0 < beta) :
-- imply
  IsErgodic (G := Multiplicative (Site d)) (independentSuperposedTraceLaw (infiniteFreeCurrentMeasure d beta hbeta.le) (infinitePlusCurrentMeasure d beta hbeta.le) : Measure (ConfigSpace (Sym2 (Site d)))) := by
-- proof
  apply StatMech.FrontierB.freePlusSuperposedTraceLaw_isErgodic hd hbeta

/--
[freePlusSuperposedTraceLaw_uniqueness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/MixedCurrentTraceFactor.lean)
-/
@[path]
private lemma freePlusSuperposedTraceLaw_uniqueness_eq
  [Countable E]
  [Group H]
  [MulAction H E]
  {d : Nat}
  {beta : Real}
-- given
  (hbeta : 0 ≤ beta)
  (hd : 1 ≤ d) :
-- imply
  let mu := (independentSuperposedTraceLaw (infiniteFreeCurrentMeasure d beta hbeta) (infinitePlusCurrentMeasure d beta hbeta) : Measure (ConfigSpace (Sym2 (Site d)))) (mu {omega | numInfiniteClusters d omega = 0} = 1 ∨ mu {omega | numInfiniteClusters d omega = 1} = 1) ∧ mu (atLeastTwoInfinite d) = 0 ∧ mu {omega | numInfiniteClusters d omega ≤ 1} = 1 := by
-- proof
  apply StatMech.FrontierB.freePlusSuperposedTraceLaw_uniqueness d beta hbeta hd


-- created on 2026-10-23
