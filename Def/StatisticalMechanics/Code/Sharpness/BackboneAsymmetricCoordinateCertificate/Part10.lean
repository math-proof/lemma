/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneAsymmetricCoordinateCertificate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneConcreteSelectorObstruction
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneAsymmetricCoordinateCertificate.Part8
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


noncomputable def CompleteBondwiseSelectorSpec.toAsymmetricCertificate
    {P : BondwiseSegmentProgram V} (R : CompleteBondwiseSelectorSpec P)
    (vacuum right₁ right₂ : BondwiseRunSpec V)
    (beta : Real) (J : Sym2 V -> Real)
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V)
    (ss : List (shb_ExplorationSegment V)) (hs : s ∈ d.active)
    (path : ContributingPathSelector d.graph beta J
      (R.toPartialSelector.sourceClass d (s :: ss))
      (stepToggleSource R.toPartialSelector d s ss)
      (R.toPartialSelector.Fiber d (s :: ss)) (liftedResidualVacuum d s)
      (shb_ActiveSegmentFiber d s hs)
      (liftedResidualFiber R.toPartialSelector d s ss))
    (path_sources : ∀ m hm,
      RandomCurrent.sources (endsM d.graph m) (path m hm) =
        stepToggleSource R.toPartialSelector d s ss)
    (vacuum_normal_form : ∀ m
      (_hm : CoordinatePairContributes R.toPartialSelector
        beta J d s ss hs m) T,
      liftedResidualVacuum d s
          (profileFlux d.graph m (univ \ T)) <->
        vacuum.Event d.graph (profileFlux d.graph m (univ \ T)))
    (right_normal_form : ∀ m
      (_hm : CoordinatePairContributes R.toPartialSelector
        beta J d s ss hs m) T,
      (shb_ActiveSegmentFiber d s hs (profileFlux d.graph m T) /\
          liftedResidualFiber R.toPartialSelector d s ss
            (profileFlux d.graph m (univ \ T))) <->
        BondwisePairEvent right₁ right₂ d.graph m T)
    (bondwise_toggle : ∀ m
      (hm : CoordinatePairContributes R.toPartialSelector
        beta J d s ss hs m) T,
      BondwisePairEvent (P.runSpec d (s :: ss)) vacuum d.graph m T <->
        BondwisePairEvent right₁ right₂ d.graph m (T ∆ path m hm)) :
    AsymmetricBondwiseCoordinateCertificate
      (P.runSpec d (s :: ss)) vacuum right₁ right₂
      R.toPartialSelector beta J d s ss hs where
  path := path
  path_sources := path_sources
  left_normal_form := by
    intro m hm T
    exact R.leftPairNormalForm vacuum d s ss m T
      (vacuum_normal_form m hm T)
  right_normal_form := right_normal_form
  bondwise_toggle := bondwise_toggle

end BackboneConcreteSelector
end
end StatMech.Sharpness
