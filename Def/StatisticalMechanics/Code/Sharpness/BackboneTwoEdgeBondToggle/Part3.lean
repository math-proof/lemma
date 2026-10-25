/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeBondToggle.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneTwoEdgeBondProgram.Part9
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneTwoEdgeBondToggle.Part2
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

def TwoUnitComponentwiseEventTable
    (d : shb_ExplorationDomain V) (e f : d.graph.edgeFinset) (hne : e ≠ f)
    (hs : canonicalEdgeSegment d.graph e ∈ d.active) : Prop :=
  let s := canonicalEdgeSegment d.graph e
  let t := canonicalEdgeSegment d.graph f
  let full := (BackboneTwoEdgeBondProgram.program (V := V)).runSpec d [s, t]
  let head := activeSegmentRunSpec d s hs
  let vacuum := residualVacuumRunSpec d s
  let suffix := (BackboneTwoEdgeBondProgram.program (V := V)).liftedResidualRunSpec d s [t]
  ((full.Event d.graph 0 <-> head.Event d.graph (unitFlux d.graph f)) /\
    (full.Event d.graph (unitFlux d.graph e) <->
      head.Event d.graph (twoUnitFlux d.graph e f)) /\
    (full.Event d.graph (unitFlux d.graph f) <-> head.Event d.graph 0) /\
    (full.Event d.graph (twoUnitFlux d.graph e f) <->
      head.Event d.graph (unitFlux d.graph e))) /\
  ((vacuum.Event d.graph 0 <->
      suffix.Event d.graph (unitFlux d.graph f)) /\
    (vacuum.Event d.graph (unitFlux d.graph e) <->
      suffix.Event d.graph (twoUnitFlux d.graph e f)) /\
    (vacuum.Event d.graph (unitFlux d.graph f) <-> suffix.Event d.graph 0) /\
    (vacuum.Event d.graph (twoUnitFlux d.graph e f) <->
      suffix.Event d.graph (unitFlux d.graph e)))


end BackboneTwoEdgeBondToggle
end
end StatMech.Sharpness
