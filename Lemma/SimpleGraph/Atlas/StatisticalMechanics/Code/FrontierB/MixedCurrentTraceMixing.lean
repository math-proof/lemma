import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierB.MixedCurrentTraceMixing
open Filter MeasureTheory Set Topology StatMech StatMech.FrontierB


/--
[infinitePlusCurrentTraceLaw_axisEventuallyGenMixing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/MixedCurrentTraceMixing.lean)
-/
@[path]
private lemma infinitePlusCurrentTraceLaw_axisEventuallyGenMixing_eq
  [Countable E]
  [Group H]
  [MulAction H E]
  {d : Nat}
  {beta : Real}
-- given
  (hd : 1 <= d)
  (hbeta : 0 < beta) :
-- imply
  fmu_AxisEventuallyGenMixing (fun k => FK.freeAxisTranslationPower hd k) (currentTraceLaw (infinitePlusCurrentMeasure d beta hbeta.le) : Measure (ConfigSpace (Sym2 (Site d)))) := by
-- proof
  apply StatMech.FrontierB.infinitePlusCurrentTraceLaw_axisEventuallyGenMixing hd hbeta

/--
[infiniteFreeCurrentTraceLaw_axisCofinalGenMixing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/MixedCurrentTraceMixing.lean)
-/
@[path]
private lemma infiniteFreeCurrentTraceLaw_axisCofinalGenMixing_eq
  [Countable E]
  [Group H]
  [MulAction H E]
  {d : Nat}
  {beta : Real}
-- given
  (hd : 1 <= d)
  (hbeta : 0 < beta) :
-- imply
  fmu_AxisCofinalGenMixing (fun k => FK.freeAxisTranslationPower hd k) (currentTraceLaw (infiniteFreeCurrentMeasure d beta hbeta.le) : Measure (ConfigSpace (Sym2 (Site d)))) := by
-- proof
  apply StatMech.FrontierB.infiniteFreeCurrentTraceLaw_axisCofinalGenMixing hd hbeta

/--
[independentMixedPairConfigLaw_real_multiOpen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/MixedCurrentTraceMixing.lean)
-/
@[path]
private lemma independentMixedPairConfigLaw_real_multiOpen_eq
  [Countable E]
  [Group H]
  [MulAction H E]
  [DecidableEq E]
  {rho nu : ProbabilityMeasure (ConfigSpace E)}
  {T : Finset (E ⊕ E)} :
-- imply
  (independentMixedPairConfigLaw rho nu : Measure _).real (fmu_multiOpen T) = (rho : Measure _).real (fmu_multiOpen (pairLeft T)) * (nu : Measure _).real (fmu_multiOpen (pairRight T)) := by
-- proof
  apply StatMech.FrontierB.independentMixedPairConfigLaw_real_multiOpen rho nu T

/--
[independentMixedPairConfigLaw_real_inter_shift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/MixedCurrentTraceMixing.lean)
-/
@[path]
private lemma independentMixedPairConfigLaw_real_inter_shift_eq
  [Countable E]
  [Group H]
  [MulAction H E]
  [DecidableEq E]
  {rho nu : ProbabilityMeasure (ConfigSpace E)}
  {g : H}
  {T U : Finset (E ⊕ E)} :
-- imply
  (independentMixedPairConfigLaw rho nu : Measure _).real (fmu_multiOpen T ∩ (shift g) ⁻¹' fmu_multiOpen U) = (rho : Measure _).real (fmu_multiOpen (pairLeft T) ∩ (shift g) ⁻¹' fmu_multiOpen (pairLeft U)) * (nu : Measure _).real (fmu_multiOpen (pairRight T) ∩ (shift g) ⁻¹' fmu_multiOpen (pairRight U)) := by
-- proof
  apply StatMech.FrontierB.independentMixedPairConfigLaw_real_inter_shift rho nu g T U

/--
[mixedPairConfig_measurePreserving](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/MixedCurrentTraceMixing.lean)
-/
@[path]
private lemma mixedPairConfig_measurePreserving_eq
  [Countable E]
  [Group H]
  [MulAction H E]
  {rho nu : ProbabilityMeasure (ConfigSpace E)} :
-- imply
  MeasurePreserving (Function.uncurry pairConfig) (rho.prod nu : Measure (ConfigSpace E × ConfigSpace E)) (independentMixedPairConfigLaw rho nu : Measure (ConfigSpace (E ⊕ E))) := by
-- proof
  apply StatMech.FrontierB.mixedPairConfig_measurePreserving rho nu

/--
[independentMixedPairConfigLaw_isTranslationInvariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/MixedCurrentTraceMixing.lean)
-/
@[path]
private lemma independentMixedPairConfigLaw_isTranslationInvariant_eq
  [Countable E]
  [Group H]
  [MulAction H E]
  {rho nu : ProbabilityMeasure (ConfigSpace E)}
-- given
  (hrho : IsTranslationInvariant (G := H) (rho : Measure (ConfigSpace E)))
  (hnu : IsTranslationInvariant (G := H) (nu : Measure (ConfigSpace E))) :
-- imply
  IsTranslationInvariant (G := H) (independentMixedPairConfigLaw rho nu : Measure (ConfigSpace (E ⊕ E))) := by
-- proof
  apply StatMech.FrontierB.independentMixedPairConfigLaw_isTranslationInvariant rho nu hrho hnu

/--
[independentMixedPairConfigLaw_pairMixing_of_axis](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/MixedCurrentTraceMixing.lean)
-/
@[path]
private lemma independentMixedPairConfigLaw_pairMixing_of_axis_eq
  [Countable E]
  [Group H]
  [MulAction H E]
  {rho nu : ProbabilityMeasure (ConfigSpace E)}
-- given
  (axis : Nat -> H)
  (hrho : fmu_AxisCofinalGenMixing axis (rho : Measure (ConfigSpace E)))
  (hnu : fmu_AxisEventuallyGenMixing axis (nu : Measure (ConfigSpace E))) :
-- imply
  fmu_PairMixing (G := H) (independentMixedPairConfigLaw rho nu : Measure (ConfigSpace (E ⊕ E))) := by
-- proof
  apply StatMech.FrontierB.independentMixedPairConfigLaw_pairMixing_of_axis axis rho nu hrho hnu

/--
[freePlusCurrentTracePairLaw_pairMixing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/MixedCurrentTraceMixing.lean)
-/
@[path]
private lemma freePlusCurrentTracePairLaw_pairMixing_eq
  [Countable E]
  [Group H]
  [MulAction H E]
  {d : Nat}
  {beta : Real}
-- given
  (hd : 1 <= d)
  (hbeta : 0 < beta) :
-- imply
  fmu_PairMixing (G := Multiplicative (Site d)) (independentMixedPairConfigLaw (currentTraceLaw (infiniteFreeCurrentMeasure d beta hbeta.le)) (currentTraceLaw (infinitePlusCurrentMeasure d beta hbeta.le)) : Measure (ConfigSpace (Sym2 (Site d) ⊕ Sym2 (Site d)))) := by
-- proof
  apply StatMech.FrontierB.freePlusCurrentTracePairLaw_pairMixing hd hbeta

/--
[freePlusCurrentTracePairLaw_genMixing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/MixedCurrentTraceMixing.lean)
-/
@[path]
private lemma freePlusCurrentTracePairLaw_genMixing_eq
  [Countable E]
  [Group H]
  [MulAction H E]
  {d : Nat}
  {beta : Real}
-- given
  (hd : 1 <= d)
  (hbeta : 0 < beta) :
-- imply
  fmu_GenMixing (G := Multiplicative (Site d)) (independentMixedPairConfigLaw (currentTraceLaw (infiniteFreeCurrentMeasure d beta hbeta.le)) (currentTraceLaw (infinitePlusCurrentMeasure d beta hbeta.le)) : Measure (ConfigSpace (Sym2 (Site d) ⊕ Sym2 (Site d)))) := by
-- proof
  apply StatMech.FrontierB.freePlusCurrentTracePairLaw_genMixing hd hbeta


-- created on 2026-10-23
