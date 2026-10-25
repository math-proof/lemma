/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeBondToggle.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneTwoEdgeBondProgram.Part9
import Def.StatisticalMechanics.Code.Sharpness.BackboneTwoEdgeBondToggle.Part3
open SimpleGraph Finset
open scoped symmDiff

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

namespace BackboneTwoEdgeBondToggle

open BackboneConcreteSelector

open BackboneConcreteBondProgram

open BackboneTwoEdgeBondProgram

open BackboneDeterminedCutSwitching

open BackboneP2CoordinateReindex

open FluxEdgeCopy

theorem twoUnit_componentwise_covariance_iff_eventTable
    (d : shb_ExplorationDomain V) (e f : d.graph.edgeFinset) (hne : e ≠ f)
    (hs : canonicalEdgeSegment d.graph e ∈ d.active) :
    (BondwiseRunToggleCovariance
        ((BackboneTwoEdgeBondProgram.program (V := V)).runSpec d
          [canonicalEdgeSegment d.graph e, canonicalEdgeSegment d.graph f])
        (activeSegmentRunSpec d (canonicalEdgeSegment d.graph e) hs)
        d.graph (twoUnitFlux d.graph e f) {secondCopy d.graph e f hne} /\
      BondwiseRunToggleCovariance
        (residualVacuumRunSpec d (canonicalEdgeSegment d.graph e))
        ((BackboneTwoEdgeBondProgram.program (V := V)).liftedResidualRunSpec d
          (canonicalEdgeSegment d.graph e)
          [canonicalEdgeSegment d.graph f])
        d.graph (twoUnitFlux d.graph e f) {secondCopy d.graph e f hne}) <->
      TwoUnitComponentwiseEventTable d e f hne hs := by
  rw [bondwiseRunToggleCovariance_twoUnit_iff,
    bondwiseRunToggleCovariance_twoUnit_iff]
  rfl


theorem twoUnit_pair_toggle_of_eventTable
    (d : shb_ExplorationDomain V) (e f : d.graph.edgeFinset) (hne : e ≠ f)
    (hs : canonicalEdgeSegment d.graph e ∈ d.active)
    (htable : TwoUnitComponentwiseEventTable d e f hne hs)
    (T : Finset (Copy d.graph (twoUnitFlux d.graph e f))) :
    BondwisePairEvent
        ((BackboneTwoEdgeBondProgram.program (V := V)).runSpec d
          [canonicalEdgeSegment d.graph e, canonicalEdgeSegment d.graph f])
        (residualVacuumRunSpec d (canonicalEdgeSegment d.graph e))
        d.graph (twoUnitFlux d.graph e f) T <->
      BondwisePairEvent
        (activeSegmentRunSpec d (canonicalEdgeSegment d.graph e) hs)
        ((BackboneTwoEdgeBondProgram.program (V := V)).liftedResidualRunSpec d
          (canonicalEdgeSegment d.graph e)
          [canonicalEdgeSegment d.graph f])
        d.graph (twoUnitFlux d.graph e f)
          (T ∆ {secondCopy d.graph e f hne}) := by
  have hcov :=
    (twoUnit_componentwise_covariance_iff_eventTable d e f hne hs).mpr htable
  exact BondwisePairEvent.toggle_iff_of_componentwise
    ((BackboneTwoEdgeBondProgram.program (V := V)).runSpec d
      [canonicalEdgeSegment d.graph e, canonicalEdgeSegment d.graph f])
    (residualVacuumRunSpec d (canonicalEdgeSegment d.graph e))
    (activeSegmentRunSpec d (canonicalEdgeSegment d.graph e) hs)
    ((BackboneTwoEdgeBondProgram.program (V := V)).liftedResidualRunSpec d
      (canonicalEdgeSegment d.graph e) [canonicalEdgeSegment d.graph f])
    d.graph (twoUnitFlux d.graph e f) {secondCopy d.graph e f hne}
    hcov.1 hcov.2 T

end BackboneTwoEdgeBondToggle
end
end StatMech.Sharpness
