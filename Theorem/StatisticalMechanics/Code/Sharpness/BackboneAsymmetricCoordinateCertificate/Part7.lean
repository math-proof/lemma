/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneAsymmetricCoordinateCertificate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneConcreteSelectorObstruction
import Def.StatisticalMechanics.Code.Sharpness.BackboneAsymmetricCoordinateCertificate.Part9
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


@[simp] theorem residualVacuumRunSpec_event
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V)
    (m : d.graph.edgeFinset -> Nat) :
    (residualVacuumRunSpec d s).Event d.graph m <->
      liftedResidualVacuum d s m := by
  exact BondwiseRunSpec.ofPredicate_event d.graph _ m

@[simp] theorem activeSegmentRunSpec_event
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V)
    (hs : s ∈ d.active) (m : d.graph.edgeFinset -> Nat) :
    (activeSegmentRunSpec d s hs).Event d.graph m <->
      shb_ActiveSegmentFiber d s hs m := by
  exact BondwiseRunSpec.ofPredicate_event d.graph _ m

@[simp] theorem BondwiseSegmentProgram.liftedResidualRunSpec_event
    (P : BondwiseSegmentProgram V)
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V)
    (word : List (shb_ExplorationSegment V))
    (m : d.graph.edgeFinset -> Nat) :
    (P.liftedResidualRunSpec d s word).Event d.graph m <->
      P.LiftedRunEvent d s word m := by
  exact BondwiseRunSpec.ofPredicate_event d.graph _ m

end BackboneConcreteSelector
end
end StatMech.Sharpness
