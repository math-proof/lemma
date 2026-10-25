/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneAsymmetricCoordinateCertificate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneConcreteSelectorObstruction
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneAsymmetricCoordinateCertificate.Part9
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


noncomputable def CompleteBondwiseSelectorSpec.toCanonicalAsymmetricCertificate
    {P : BondwiseSegmentProgram V} (R : CompleteBondwiseSelectorSpec P)
    (beta : Real) (J : Sym2 V -> Real)
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V)
    (ss : List (shb_ExplorationSegment V)) (hs : s ∈ d.active)
    (path : ContributingPathSelector d.graph beta J
      (R.toPartialSelector.sourceClass d (s :: ss))
      (stepToggleSource R.toPartialSelector d s ss)
      (R.toPartialSelector.Fiber d (s :: ss)) (liftedResidualVacuum d s)
      (shb_ActiveSegmentFiber d s hs)
      (liftedResidualFiber R.toPartialSelector d s ss))
    (bondwise_toggle : ∀ m
      (hm : CoordinatePairContributes R.toPartialSelector
        beta J d s ss hs m) T,
      BondwisePairEvent (P.runSpec d (s :: ss))
          (residualVacuumRunSpec d s) d.graph m T <->
        BondwisePairEvent (activeSegmentRunSpec d s hs)
          (P.liftedResidualRunSpec d s ss) d.graph m (T ∆ path m hm)) :
    AsymmetricBondwiseCoordinateCertificate
      (P.runSpec d (s :: ss)) (residualVacuumRunSpec d s)
      (activeSegmentRunSpec d s hs) (P.liftedResidualRunSpec d s ss)
      R.toPartialSelector beta J d s ss hs :=
  R.toAsymmetricCertificate
    (residualVacuumRunSpec d s) (activeSegmentRunSpec d s hs)
    (P.liftedResidualRunSpec d s ss) beta J d s ss hs path
    (R.path_sources_of_canonical_toggle beta J d s ss hs path bondwise_toggle)
    (by
      intro m _ T
      exact (residualVacuumRunSpec_event d s
        (profileFlux d.graph m (univ \ T))).symm)
    (by
      intro m _ T
      exact R.rightPairNormalForm
        (activeSegmentRunSpec d s hs) (P.liftedResidualRunSpec d s ss)
        d s ss hs m T
        (activeSegmentRunSpec_event d s hs
          (profileFlux d.graph m T)).symm
        (P.liftedResidualRunSpec_event d s ss
          (profileFlux d.graph m (univ \ T))).symm)
    bondwise_toggle


def CompleteBondwiseSelectorSpec.CanonicalBondwiseToggleExists
    {P : BondwiseSegmentProgram V} (R : CompleteBondwiseSelectorSpec P)
    (beta : Real) (J : Sym2 V -> Real)
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V)
    (ss : List (shb_ExplorationSegment V)) (hs : s ∈ d.active) : Prop :=
  ∀ m,
    CoordinatePairContributes R.toPartialSelector beta J d s ss hs m ->
      ∃ path : Finset (Copy d.graph m), ∀ T,
        BondwisePairEvent (P.runSpec d (s :: ss))
            (residualVacuumRunSpec d s) d.graph m T <->
          BondwisePairEvent (activeSegmentRunSpec d s hs)
            (P.liftedResidualRunSpec d s ss) d.graph m (T ∆ path)


def CompleteBondwiseSelectorSpec.CanonicalComponentwiseToggleExists
    {P : BondwiseSegmentProgram V} (R : CompleteBondwiseSelectorSpec P)
    (beta : Real) (J : Sym2 V -> Real)
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V)
    (ss : List (shb_ExplorationSegment V)) (hs : s ∈ d.active) : Prop :=
  ∀ m,
    CoordinatePairContributes R.toPartialSelector beta J d s ss hs m ->
      ∃ path : Finset (Copy d.graph m),
        BondwiseRunToggleCovariance (P.runSpec d (s :: ss))
            (activeSegmentRunSpec d s hs) d.graph m path /\
          BondwiseRunToggleCovariance (residualVacuumRunSpec d s)
            (P.liftedResidualRunSpec d s ss) d.graph m path


end BackboneConcreteSelector
end
end StatMech.Sharpness
