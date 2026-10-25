/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneAsymmetricCoordinateCertificate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneConcreteSelectorObstruction
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneAsymmetricCoordinateCertificate.Part10
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


noncomputable def
    CompleteBondwiseSelectorSpec.toCanonicalAsymmetricCertificate_of_toggleExists
    {P : BondwiseSegmentProgram V} (R : CompleteBondwiseSelectorSpec P)
    (beta : Real) (J : Sym2 V -> Real)
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V)
    (ss : List (shb_ExplorationSegment V)) (hs : s ∈ d.active)
    (h : R.CanonicalBondwiseToggleExists beta J d s ss hs) :
    AsymmetricBondwiseCoordinateCertificate
      (P.runSpec d (s :: ss)) (residualVacuumRunSpec d s)
      (activeSegmentRunSpec d s hs) (P.liftedResidualRunSpec d s ss)
      R.toPartialSelector beta J d s ss hs := by
  let path : ContributingPathSelector d.graph beta J
      (R.toPartialSelector.sourceClass d (s :: ss))
      (stepToggleSource R.toPartialSelector d s ss)
      (R.toPartialSelector.Fiber d (s :: ss)) (liftedResidualVacuum d s)
      (shb_ActiveSegmentFiber d s hs)
      (liftedResidualFiber R.toPartialSelector d s ss) :=
    fun m hm => Classical.choose (h m hm)
  apply R.toCanonicalAsymmetricCertificate beta J d s ss hs path
  intro m hm T
  simpa only [path] using (Classical.choose_spec (h m hm) T)


noncomputable def
    CompleteBondwiseSelectorSpec.toCanonicalAsymmetricCertificate_of_componentwise
    {P : BondwiseSegmentProgram V} (R : CompleteBondwiseSelectorSpec P)
    (beta : Real) (J : Sym2 V -> Real)
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V)
    (ss : List (shb_ExplorationSegment V)) (hs : s ∈ d.active)
    (h : R.CanonicalComponentwiseToggleExists beta J d s ss hs) :
    AsymmetricBondwiseCoordinateCertificate
      (P.runSpec d (s :: ss)) (residualVacuumRunSpec d s)
      (activeSegmentRunSpec d s hs) (P.liftedResidualRunSpec d s ss)
      R.toPartialSelector beta J d s ss hs :=
  R.toCanonicalAsymmetricCertificate_of_toggleExists beta J d s ss hs
    (R.canonicalToggleExists_of_componentwise beta J d s ss hs h)


end BackboneConcreteSelector
end
end StatMech.Sharpness
