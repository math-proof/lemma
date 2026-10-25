/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/SuperposedTraceErgodicity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.PlusCurrentFamilyMixing.Part3
import Theorem.StatisticalMechanics.Code.FK.FKMixingUpperClose.Part5
import Def.StatisticalMechanics.Code.FrontierB.SuperposedTraceErgodicity.Part5
open MeasureTheory Set


namespace StatMech.FrontierB

open ConfigSpace StatMech.FK

variable {E H : Type*} [Countable E] [Group H] [MulAction H E]


theorem pairOrConfig_measurePreserving
    (rho : ProbabilityMeasure (ConfigSpace E)) :
    MeasurePreserving pairOrConfig
      (independentPairConfigLaw rho : Measure (ConfigSpace (E ⊕ E)))
      (independentOrConfigLaw rho : Measure (ConfigSpace E)) := by
  change MeasurePreserving pairOrConfig _
    (Measure.map pairOrConfig
      (independentPairConfigLaw rho : Measure (ConfigSpace (E ⊕ E))))
  exact measurable_pairOrConfig.measurePreserving _


theorem independentOrConfigLaw_isErgodic
    (rho : ProbabilityMeasure (ConfigSpace E))
    (herg : IsErgodic (G := H)
      (independentPairConfigLaw rho : Measure (ConfigSpace (E ⊕ E)))) :
    IsErgodic (G := H)
      (independentOrConfigLaw rho : Measure (ConfigSpace E)) := by
  refine ⟨fun g => (pairOrConfig_measurePreserving rho).of_semiconj
    (herg.1 g) (pairOrConfig_shift g) (measurable_shift g), ?_⟩
  intro s hs hinv
  have hfactor := pairOrConfig_measurePreserving rho
  have hpre : MeasurableSet (pairOrConfig ⁻¹' s) :=
    measurable_pairOrConfig hs
  have hpreInv : ∀ g : H,
      (shift g) ⁻¹' (pairOrConfig ⁻¹' s) = pairOrConfig ⁻¹' s := by
    intro g
    ext omega
    change shift g (pairOrConfig omega) ∈ s ↔ pairOrConfig omega ∈ s
    exact Set.ext_iff.mp (hinv g) (pairOrConfig omega)
  rcases herg.2 (pairOrConfig ⁻¹' s) hpre hpreInv with hzero | hfull
  · left
    rw [← hfactor.measure_preimage hs.nullMeasurableSet]
    exact hzero
  · right
    rw [← hfactor.measure_preimage hs.nullMeasurableSet,
      ← hfactor.measure_preimage MeasurableSet.univ.nullMeasurableSet]
    exact hfull

theorem independentOrConfigLaw_isErgodic_of_genMixing
    (rho : ProbabilityMeasure (ConfigSpace E))
    (hti : IsTranslationInvariant (G := H) (rho : Measure (ConfigSpace E)))
    (hmix : fmu_GenMixing (G := H) (rho : Measure (ConfigSpace E))) :
    IsErgodic (G := H)
      (independentOrConfigLaw rho : Measure (ConfigSpace E)) :=
  independentOrConfigLaw_isErgodic rho
    (independentPairConfigLaw_isErgodic rho hti hmix)


theorem independentOr_currentTraceLaw_eq_superposed
    (mu : ProbabilityMeasure (InfiniteCurrentConfig E)) :
    (independentOrConfigLaw (currentTraceLaw mu) : Measure (ConfigSpace E)) =
      (independentSuperposedTraceLaw mu mu : Measure (ConfigSpace E)) := by
  change Measure.map pairOrConfig
      (Measure.map (Function.uncurry pairConfig)
        ((Measure.map currentTrace (mu : Measure _)).prod
          (Measure.map currentTrace (mu : Measure _)))) =
    Measure.map superposedCurrentTrace
      ((mu : Measure (InfiniteCurrentConfig E)).prod
        (mu : Measure (InfiniteCurrentConfig E)))
  rw [Measure.map_prod_map (mu : Measure (InfiniteCurrentConfig E))
    (mu : Measure (InfiniteCurrentConfig E))
    continuous_currentTrace.measurable continuous_currentTrace.measurable]
  rw [Measure.map_map measurable_pairConfig
      (continuous_currentTrace.measurable.prodMap
        continuous_currentTrace.measurable),
    Measure.map_map measurable_pairOrConfig
      (measurable_pairConfig.comp
        (continuous_currentTrace.measurable.prodMap
          continuous_currentTrace.measurable))]
  congr 1
  funext p e
  change (decide (0 < p.1 e) || decide (0 < p.2 e)) =
    decide (0 < p.1 e + p.2 e)
  simp


theorem independentSuperposedTraceLaw_self_isErgodic_of_cylinderPairMixing
    (mu : ProbabilityMeasure (InfiniteCurrentConfig E))
    (hti : CurrentIsTranslationInvariant (H := H)
      (mu : Measure (InfiniteCurrentConfig E)))
    (hmix : CurrentCylinderPairMixing (H := H)
      (mu : Measure (InfiniteCurrentConfig E))) :
    IsErgodic (G := H)
      (independentSuperposedTraceLaw mu mu : Measure (ConfigSpace E)) := by
  rw [← independentOr_currentTraceLaw_eq_superposed]
  exact independentOrConfigLaw_isErgodic_of_genMixing (currentTraceLaw mu)
    (hti.trace mu) (currentTraceLaw_genMixing mu hmix)


theorem plusPlusSuperposedTraceLaw_isErgodic {d : Nat}
    (hd : 1 ≤ d) {beta : Real} (hbeta : 0 < beta) :
    IsErgodic (G := Multiplicative (Lattice.Site d))
      (independentSuperposedTraceLaw
        (infinitePlusCurrentMeasure d beta hbeta.le)
        (infinitePlusCurrentMeasure d beta hbeta.le) :
          Measure (ConfigSpace (Sym2 (Lattice.Site d)))) :=
  independentSuperposedTraceLaw_self_isErgodic_of_cylinderPairMixing _
    (infinitePlusCurrentMeasure_isTranslationInvariant d beta hbeta)
    (infinitePlusCurrentMeasure_cylinderPairMixing hd hbeta)


end StatMech.FrontierB
