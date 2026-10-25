/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneAsymmetricCoordinateCertificate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneConcreteSelectorObstruction
import Instance.StatisticalMechanics.Code.Sharpness.BackboneAsymmetricCoordinateCertificate.Part4
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


theorem CompleteBondwiseSelectorSpec.liftedResidualFiber_iff_liftedRunEvent
    {P : BondwiseSegmentProgram V} (R : CompleteBondwiseSelectorSpec P)
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V)
    (word : List (shb_ExplorationSegment V))
    (q : d.graph.edgeFinset -> Nat) :
    liftedResidualFiber R.toPartialSelector d s word q <->
      P.LiftedRunEvent d s word q := by
  constructor
  · rintro ⟨r, hr, hfiber⟩
    exact ⟨r, hr, (R.fiber_iff_runSpec_event
      (shb_BackboneExplorationDomain.advance d s) word r).mp hfiber⟩
  · rintro ⟨r, hr, hrun⟩
    exact ⟨r, hr, (R.fiber_iff_runSpec_event
      (shb_BackboneExplorationDomain.advance d s) word r).mpr hrun⟩


theorem CompleteBondwiseSelectorSpec.leftPairNormalForm
    {P : BondwiseSegmentProgram V} (R : CompleteBondwiseSelectorSpec P)
    (vacuum : BondwiseRunSpec V)
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V)
    (ss : List (shb_ExplorationSegment V))
    (m : d.graph.edgeFinset -> Nat) (T : Finset (Copy d.graph m))
    (hvacuum :
      liftedResidualVacuum d s
          (profileFlux d.graph m (univ \ T)) <->
        vacuum.Event d.graph (profileFlux d.graph m (univ \ T))) :
    (R.toPartialSelector.Fiber d (s :: ss)
          (profileFlux d.graph m T) /\
        liftedResidualVacuum d s
          (profileFlux d.graph m (univ \ T))) <->
      BondwisePairEvent (P.runSpec d (s :: ss)) vacuum d.graph m T := by
  exact and_congr
    (R.fiber_iff_runSpec_event d (s :: ss) (profileFlux d.graph m T))
    hvacuum


theorem CompleteBondwiseSelectorSpec.rightPairNormalForm
    {P : BondwiseSegmentProgram V} (R : CompleteBondwiseSelectorSpec P)
    (head residual : BondwiseRunSpec V)
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V)
    (ss : List (shb_ExplorationSegment V)) (hs : s ∈ d.active)
    (m : d.graph.edgeFinset -> Nat) (T : Finset (Copy d.graph m))
    (hhead :
      shb_ActiveSegmentFiber d s hs (profileFlux d.graph m T) <->
        head.Event d.graph (profileFlux d.graph m T))
    (hresidual :
      P.LiftedRunEvent d s ss (profileFlux d.graph m (univ \ T)) <->
        residual.Event d.graph (profileFlux d.graph m (univ \ T))) :
    (shb_ActiveSegmentFiber d s hs (profileFlux d.graph m T) /\
        liftedResidualFiber R.toPartialSelector d s ss
          (profileFlux d.graph m (univ \ T))) <->
      BondwisePairEvent head residual d.graph m T := by
  exact and_congr hhead
    ((R.liftedResidualFiber_iff_liftedRunEvent d s ss
      (profileFlux d.graph m (univ \ T))).trans hresidual)


end BackboneConcreteSelector
end
end StatMech.Sharpness
