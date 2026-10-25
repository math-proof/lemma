/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneAsymmetricCoordinateCertificate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneConcreteSelectorObstruction
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneAsymmetricCoordinateCertificate.Part6
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


def BondwiseSegmentProgram.LiftedRunEvent
    (P : BondwiseSegmentProgram V)
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V)
    (word : List (shb_ExplorationSegment V)) :
    (d.graph.edgeFinset -> Nat) -> Prop :=
  LiftedPredicate (d.graph.deleteEdges_le s.edgeSet)
    ((P.runSpec (shb_BackboneExplorationDomain.advance d s) word).Event
      (shb_BackboneExplorationDomain.advance d s).graph)


noncomputable def residualVacuumRunSpec
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V) :
    BondwiseRunSpec V :=
  BondwiseRunSpec.ofPredicate d.graph (liftedResidualVacuum d s)


noncomputable def activeSegmentRunSpec
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V)
    (hs : s ∈ d.active) : BondwiseRunSpec V :=
  BondwiseRunSpec.ofPredicate d.graph (shb_ActiveSegmentFiber d s hs)


noncomputable def BondwiseSegmentProgram.liftedResidualRunSpec
    (P : BondwiseSegmentProgram V)
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V)
    (word : List (shb_ExplorationSegment V)) : BondwiseRunSpec V :=
  BondwiseRunSpec.ofPredicate d.graph (P.LiftedRunEvent d s word)

end BackboneConcreteSelector
end
end StatMech.Sharpness
