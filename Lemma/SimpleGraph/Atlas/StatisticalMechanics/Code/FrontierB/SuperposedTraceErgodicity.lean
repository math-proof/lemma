import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierB.SuperposedTraceErgodicity
open MeasureTheory Set StatMech StatMech.FrontierB


/--
[currentTrace_preimage_cylinder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/SuperposedTraceErgodicity.lean)
-/
@[path]
private lemma currentTrace_preimage_cylinder_eq
  [Countable E]
  [Group H]
  [MulAction H E]
  {S : Finset E}
-- given
  (A : Set (↑S -> Bool)) :
-- imply
  currentTrace ⁻¹' MeasureTheory.cylinder S A = currentCylinder S (tracePullbackPatternSet S A) := by
-- proof
  apply StatMech.FrontierB.currentTrace_preimage_cylinder S A

/--
[currentTrace_preimage_mem_measurableCylinders](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/SuperposedTraceErgodicity.lean)
-/
@[path]
private lemma currentTrace_preimage_mem_measurableCylinders_eq
  [Countable E]
  [Group H]
  [MulAction H E]
  {C : Set (ConfigSpace E)}
-- given
  (hC : C ∈ measurableCylinders (fun _ : E => Bool)) :
-- imply
  currentTrace ⁻¹' C ∈ measurableCylinders (fun _ : E => Nat) := by
-- proof
  apply StatMech.FrontierB.currentTrace_preimage_mem_measurableCylinders hC

/--
[currentTraceLaw_real](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/SuperposedTraceErgodicity.lean)
-/
@[path]
private lemma currentTraceLaw_real_eq
  [Countable E]
  [Group H]
  [MulAction H E]
  {mu : ProbabilityMeasure (InfiniteCurrentConfig E)}
  {A : Set (ConfigSpace E)}
-- given
  (hA : MeasurableSet A) :
-- imply
  (currentTraceLaw mu : Measure (ConfigSpace E)).real A = (mu : Measure (InfiniteCurrentConfig E)).real (currentTrace ⁻¹' A) := by
-- proof
  apply StatMech.FrontierB.currentTraceLaw_real mu hA

/--
[currentTrace_preimage_inter_shift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/SuperposedTraceErgodicity.lean)
-/
@[path]
private lemma currentTrace_preimage_inter_shift_eq
  [Countable E]
  [Group H]
  [MulAction H E]
  {g : H}
  {A B : Set (ConfigSpace E)} :
-- imply
  currentTrace ⁻¹' (A ∩ (shift g) ⁻¹' B) = (currentTrace ⁻¹' A) ∩ (currentShift g) ⁻¹' (currentTrace ⁻¹' B) := by
-- proof
  apply StatMech.FrontierB.currentTrace_preimage_inter_shift g A B

/--
[currentTraceLaw_genMixing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/SuperposedTraceErgodicity.lean)
-/
@[path]
private lemma currentTraceLaw_genMixing_eq
  [Countable E]
  [Group H]
  [MulAction H E]
  {mu : ProbabilityMeasure (InfiniteCurrentConfig E)}
-- given
  (hmix : CurrentCylinderPairMixing (H := H) (mu : Measure (InfiniteCurrentConfig E))) :
-- imply
  fmu_GenMixing (G := H) (currentTraceLaw mu : Measure (ConfigSpace E)) := by
-- proof
  apply StatMech.FrontierB.currentTraceLaw_genMixing mu hmix

/--
[infinitePlusCurrentTraceLaw_genMixing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/SuperposedTraceErgodicity.lean)
-/
@[path]
private lemma infinitePlusCurrentTraceLaw_genMixing_eq
  [Countable E]
  [Group H]
  [MulAction H E]
  {d : Nat}
  {beta : Real}
-- given
  (hd : 1 ≤ d)
  (hbeta : 0 < beta) :
-- imply
  fmu_GenMixing (G := Multiplicative (Lattice.Site d)) (currentTraceLaw (infinitePlusCurrentMeasure d beta hbeta.le) : Measure (ConfigSpace (Sym2 (Lattice.Site d)))) := by
-- proof
  apply StatMech.FrontierB.infinitePlusCurrentTraceLaw_genMixing hd hbeta

/--
[measurable_pairConfig](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/SuperposedTraceErgodicity.lean)
-/
@[path]
private lemma measurable_pairConfig_eq
  [Countable E]
  [Group H]
  [MulAction H E] :
-- imply
  Measurable (Function.uncurry pairConfig : ConfigSpace E × ConfigSpace E -> ConfigSpace (E ⊕ E)) := by
-- proof
  apply StatMech.FrontierB.measurable_pairConfig

/--
[pairConfig_shift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/SuperposedTraceErgodicity.lean)
-/
@[path]
private lemma pairConfig_shift_eq
  [Countable E]
  [Group H]
  [MulAction H E]
  {g : H}
  {omega eta : ConfigSpace E} :
-- imply
  pairConfig (shift g omega) (shift g eta) = shift g (pairConfig omega eta) := by
-- proof
  apply StatMech.FrontierB.pairConfig_shift g omega eta

/--
[pairConfig_preimage_multiOpen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/SuperposedTraceErgodicity.lean)
-/
@[path]
private lemma pairConfig_preimage_multiOpen_eq
  [Countable E]
  [Group H]
  [MulAction H E]
  [DecidableEq E]
  {T : Finset (E ⊕ E)} :
-- imply
  Function.uncurry pairConfig ⁻¹' fmu_multiOpen T = fmu_multiOpen (pairLeft T) ×ˢ fmu_multiOpen (pairRight T) := by
-- proof
  apply StatMech.FrontierB.pairConfig_preimage_multiOpen T

/--
[independentPairConfigLaw_real_multiOpen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/SuperposedTraceErgodicity.lean)
-/
@[path]
private lemma independentPairConfigLaw_real_multiOpen_eq
  [Countable E]
  [Group H]
  [MulAction H E]
  [DecidableEq E]
  {rho : ProbabilityMeasure (ConfigSpace E)}
  {T : Finset (E ⊕ E)} :
-- imply
  (independentPairConfigLaw rho : Measure _).real (fmu_multiOpen T) = (rho : Measure _).real (fmu_multiOpen (pairLeft T)) * (rho : Measure _).real (fmu_multiOpen (pairRight T)) := by
-- proof
  apply StatMech.FrontierB.independentPairConfigLaw_real_multiOpen rho T

/--
[pairConfig_preimage_multiOpen_inter_shift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/SuperposedTraceErgodicity.lean)
-/
@[path]
private lemma pairConfig_preimage_multiOpen_inter_shift_eq
  [Countable E]
  [Group H]
  [MulAction H E]
  [DecidableEq E]
  {g : H}
  {T U : Finset (E ⊕ E)} :
-- imply
  Function.uncurry pairConfig ⁻¹' (fmu_multiOpen T ∩ (shift g) ⁻¹' fmu_multiOpen U) = (fmu_multiOpen (pairLeft T) ∩ (shift g) ⁻¹' fmu_multiOpen (pairLeft U)) ×ˢ (fmu_multiOpen (pairRight T) ∩ (shift g) ⁻¹' fmu_multiOpen (pairRight U)) := by
-- proof
  apply StatMech.FrontierB.pairConfig_preimage_multiOpen_inter_shift g T U

/--
[independentPairConfigLaw_real_inter_shift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/SuperposedTraceErgodicity.lean)
-/
@[path]
private lemma independentPairConfigLaw_real_inter_shift_eq
  [Countable E]
  [Group H]
  [MulAction H E]
  [DecidableEq E]
  {rho : ProbabilityMeasure (ConfigSpace E)}
  {g : H}
  {T U : Finset (E ⊕ E)} :
-- imply
  (independentPairConfigLaw rho : Measure _).real (fmu_multiOpen T ∩ (shift g) ⁻¹' fmu_multiOpen U) = (rho : Measure _).real (fmu_multiOpen (pairLeft T) ∩ (shift g) ⁻¹' fmu_multiOpen (pairLeft U)) * (rho : Measure _).real (fmu_multiOpen (pairRight T) ∩ (shift g) ⁻¹' fmu_multiOpen (pairRight U)) := by
-- proof
  apply StatMech.FrontierB.independentPairConfigLaw_real_inter_shift rho g T U

/--
[independentPairConfigLaw_pairMixing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/SuperposedTraceErgodicity.lean)
-/
@[path]
private lemma independentPairConfigLaw_pairMixing_eq
  [Countable E]
  [Group H]
  [MulAction H E]
  {rho : ProbabilityMeasure (ConfigSpace E)}
-- given
  (hmix : fmu_GenMixing (G := H) (rho : Measure (ConfigSpace E))) :
-- imply
  fmu_PairMixing (G := H) (independentPairConfigLaw rho : Measure (ConfigSpace (E ⊕ E))) := by
-- proof
  apply StatMech.FrontierB.independentPairConfigLaw_pairMixing rho hmix

/--
[pairConfig_measurePreserving](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/SuperposedTraceErgodicity.lean)
-/
@[path]
private lemma pairConfig_measurePreserving_eq
  [Countable E]
  [Group H]
  [MulAction H E]
  {rho : ProbabilityMeasure (ConfigSpace E)} :
-- imply
  MeasurePreserving (Function.uncurry pairConfig) (rho.prod rho : Measure (ConfigSpace E × ConfigSpace E)) (independentPairConfigLaw rho : Measure (ConfigSpace (E ⊕ E))) := by
-- proof
  apply StatMech.FrontierB.pairConfig_measurePreserving rho

/--
[independentPairConfigLaw_isTranslationInvariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/SuperposedTraceErgodicity.lean)
-/
@[path]
private lemma independentPairConfigLaw_isTranslationInvariant_eq
  [Countable E]
  [Group H]
  [MulAction H E]
  {rho : ProbabilityMeasure (ConfigSpace E)}
-- given
  (hti : IsTranslationInvariant (G := H) (rho : Measure (ConfigSpace E))) :
-- imply
  IsTranslationInvariant (G := H) (independentPairConfigLaw rho : Measure (ConfigSpace (E ⊕ E))) := by
-- proof
  apply StatMech.FrontierB.independentPairConfigLaw_isTranslationInvariant rho hti

/--
[independentPairConfigLaw_isErgodic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/SuperposedTraceErgodicity.lean)
-/
@[path]
private lemma independentPairConfigLaw_isErgodic_eq
  [Countable E]
  [Group H]
  [MulAction H E]
  {rho : ProbabilityMeasure (ConfigSpace E)}
-- given
  (hti : IsTranslationInvariant (G := H) (rho : Measure (ConfigSpace E)))
  (hmix : fmu_GenMixing (G := H) (rho : Measure (ConfigSpace E))) :
-- imply
  IsErgodic (G := H) (independentPairConfigLaw rho : Measure (ConfigSpace (E ⊕ E))) := by
-- proof
  apply StatMech.FrontierB.independentPairConfigLaw_isErgodic rho hti hmix

/--
[measurable_pairOrConfig](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/SuperposedTraceErgodicity.lean)
-/
@[path]
private lemma measurable_pairOrConfig_eq
  [Countable E]
  [Group H]
  [MulAction H E] :
-- imply
  Measurable (pairOrConfig : ConfigSpace (E ⊕ E) -> ConfigSpace E) := by
-- proof
  apply StatMech.FrontierB.measurable_pairOrConfig

/--
[pairOrConfig_shift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/SuperposedTraceErgodicity.lean)
-/
@[path]
private lemma pairOrConfig_shift_eq
  [Countable E]
  [Group H]
  [MulAction H E]
  {g : H} :
-- imply
  Function.Semiconj (pairOrConfig : ConfigSpace (E ⊕ E) -> ConfigSpace E) (shift g) (shift g) := by
-- proof
  apply StatMech.FrontierB.pairOrConfig_shift g

/--
[pairOrConfig_measurePreserving](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/SuperposedTraceErgodicity.lean)
-/
@[path]
private lemma pairOrConfig_measurePreserving_eq
  [Countable E]
  [Group H]
  [MulAction H E]
  {rho : ProbabilityMeasure (ConfigSpace E)} :
-- imply
  MeasurePreserving pairOrConfig (independentPairConfigLaw rho : Measure (ConfigSpace (E ⊕ E))) (independentOrConfigLaw rho : Measure (ConfigSpace E)) := by
-- proof
  apply StatMech.FrontierB.pairOrConfig_measurePreserving rho

/--
[independentOrConfigLaw_isErgodic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/SuperposedTraceErgodicity.lean)
-/
@[path]
private lemma independentOrConfigLaw_isErgodic_eq
  [Countable E]
  [Group H]
  [MulAction H E]
  {rho : ProbabilityMeasure (ConfigSpace E)}
-- given
  (herg : IsErgodic (G := H) (independentPairConfigLaw rho : Measure (ConfigSpace (E ⊕ E)))) :
-- imply
  IsErgodic (G := H) (independentOrConfigLaw rho : Measure (ConfigSpace E)) := by
-- proof
  apply StatMech.FrontierB.independentOrConfigLaw_isErgodic rho herg

/--
[independentOrConfigLaw_isErgodic_of_genMixing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/SuperposedTraceErgodicity.lean)
-/
@[path]
private lemma independentOrConfigLaw_isErgodic_of_genMixing_eq
  [Countable E]
  [Group H]
  [MulAction H E]
  {rho : ProbabilityMeasure (ConfigSpace E)}
-- given
  (hti : IsTranslationInvariant (G := H) (rho : Measure (ConfigSpace E)))
  (hmix : fmu_GenMixing (G := H) (rho : Measure (ConfigSpace E))) :
-- imply
  IsErgodic (G := H) (independentOrConfigLaw rho : Measure (ConfigSpace E)) := by
-- proof
  apply StatMech.FrontierB.independentOrConfigLaw_isErgodic_of_genMixing rho hti hmix

/--
[independentOr_currentTraceLaw_eq_superposed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/SuperposedTraceErgodicity.lean)
-/
@[path]
private lemma independentOr_currentTraceLaw_eq_superposed_eq
  [Countable E]
  [Group H]
  [MulAction H E]
  {mu : ProbabilityMeasure (InfiniteCurrentConfig E)} :
-- imply
  (independentOrConfigLaw (currentTraceLaw mu) : Measure (ConfigSpace E)) = (independentSuperposedTraceLaw mu mu : Measure (ConfigSpace E)) := by
-- proof
  apply StatMech.FrontierB.independentOr_currentTraceLaw_eq_superposed mu

/--
[independentSuperposedTraceLaw_self_isErgodic_of_cylinderPairMixing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/SuperposedTraceErgodicity.lean)
-/
@[path]
private lemma independentSuperposedTraceLaw_self_isErgodic_of_cylinderPairMixing_eq
  [Countable E]
  [Group H]
  [MulAction H E]
  {mu : ProbabilityMeasure (InfiniteCurrentConfig E)}
-- given
  (hti : CurrentIsTranslationInvariant (H := H) (mu : Measure (InfiniteCurrentConfig E)))
  (hmix : CurrentCylinderPairMixing (H := H) (mu : Measure (InfiniteCurrentConfig E))) :
-- imply
  IsErgodic (G := H) (independentSuperposedTraceLaw mu mu : Measure (ConfigSpace E)) := by
-- proof
  apply StatMech.FrontierB.independentSuperposedTraceLaw_self_isErgodic_of_cylinderPairMixing mu hti hmix

/--
[plusPlusSuperposedTraceLaw_isErgodic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/SuperposedTraceErgodicity.lean)
-/
@[path]
private lemma plusPlusSuperposedTraceLaw_isErgodic_eq
  [Countable E]
  [Group H]
  [MulAction H E]
  {d : Nat}
  {beta : Real}
-- given
  (hd : 1 ≤ d)
  (hbeta : 0 < beta) :
-- imply
  IsErgodic (G := Multiplicative (Lattice.Site d)) (independentSuperposedTraceLaw (infinitePlusCurrentMeasure d beta hbeta.le) (infinitePlusCurrentMeasure d beta hbeta.le) : Measure (ConfigSpace (Sym2 (Lattice.Site d)))) := by
-- proof
  apply StatMech.FrontierB.plusPlusSuperposedTraceLaw_isErgodic hd hbeta


-- created on 2026-10-23
