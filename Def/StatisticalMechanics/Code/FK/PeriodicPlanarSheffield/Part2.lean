/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffield.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarCoverage.Part3
import Theorem.StatisticalMechanics.Code.FK.ContinuousRectangleCrossing.Part9
import Theorem.StatisticalMechanics.Code.Foundations.Ergodicity.Part2
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffield
open Filter MeasureTheory Set SimpleGraph Topology


namespace StatMech.FK.PeriodicPlanar

open BeffaraDC Lattice

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}


noncomputable def PeriodicPlaneEmbedding.fundamentalArcDisplacements
    (E : PeriodicPlaneEmbedding P) : Set (Fin 2 → ℝ) := by
  letI : SimpleGraph.LocallyFinite P.graph := P.locallyFinite
  letI : DecidableRel P.graph.Adj := Classical.decRel _
  exact ⋃ u ∈ P.fundamentalDomain, ⋃ y ∈ P.graph.neighborFinset u,
    if h : P.graph.Adj u y then
      Set.range (fun t => E.coordinates (E.edgeArc h t - E.vertex u))
    else ∅

end StatMech.FK.PeriodicPlanar
