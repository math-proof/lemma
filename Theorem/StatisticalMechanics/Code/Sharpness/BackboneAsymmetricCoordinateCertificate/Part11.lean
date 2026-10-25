/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneAsymmetricCoordinateCertificate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneConcreteSelectorObstruction
import Def.StatisticalMechanics.Code.Sharpness.BackboneAsymmetricCoordinateCertificate.Part12
open SimpleGraph Finset BigOperators
open scoped symmDiff

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

namespace BackboneConcreteSelector

open BackboneDeterminedCutSwitching

open BackbonePartialP2Reindex

open BackboneP2CoordinateReindex

open BackboneP2CoordinateToggleObstruction

open FluxEdgeCopy

variable {D : Type*}


theorem CompleteBondwiseSelectorSpec.nonempty_canonicalCertificate_iff_toggleExists
    {P : BondwiseSegmentProgram V} (R : CompleteBondwiseSelectorSpec P)
    (beta : Real) (J : Sym2 V -> Real)
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V)
    (ss : List (shb_ExplorationSegment V)) (hs : s ∈ d.active) :
    Nonempty (AsymmetricBondwiseCoordinateCertificate
      (P.runSpec d (s :: ss)) (residualVacuumRunSpec d s)
      (activeSegmentRunSpec d s hs) (P.liftedResidualRunSpec d s ss)
      R.toPartialSelector beta J d s ss hs) <->
      R.CanonicalBondwiseToggleExists beta J d s ss hs := by
  constructor
  · rintro ⟨C⟩ m hm
    exact ⟨C.path m hm, C.bondwise_toggle m hm⟩
  · intro h
    exact ⟨R.toCanonicalAsymmetricCertificate_of_toggleExists
      beta J d s ss hs h⟩


theorem CompleteBondwiseSelectorSpec.not_toggleExists_of_clearedP2_ne
    {P : BondwiseSegmentProgram V} (R : CompleteBondwiseSelectorSpec P)
    (beta : Real) (J : Sym2 V -> Real)
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V)
    (ss : List (shb_ExplorationSegment V)) (hs : s ∈ d.active)
    (hne : R.toPartialSelector.actualMass beta J d (s :: ss) *
          currentSum (shb_BackboneExplorationDomain.advance d s).graph
            beta J ∅ ≠
        shb_segmentNum beta J d s *
          R.toPartialSelector.actualMass beta J
            (shb_BackboneExplorationDomain.advance d s) ss) :
    ¬ R.CanonicalBondwiseToggleExists beta J d s ss hs := by
  intro h
  let C := R.toCanonicalAsymmetricCertificate_of_toggleExists
    beta J d s ss hs h
  exact hne (C.actualMass_active
    (P.runSpec d (s :: ss)) (residualVacuumRunSpec d s)
    (activeSegmentRunSpec d s hs) (P.liftedResidualRunSpec d s ss)
    R.toPartialSelector beta J d s ss hs)


end BackboneConcreteSelector
end
end StatMech.Sharpness
