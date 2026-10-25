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
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarSheffield.Part6
open Filter MeasureTheory Set SimpleGraph Topology


namespace StatMech.FK.PeriodicPlanar

open BeffaraDC Lattice

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}


theorem PeriodicPlaneEmbedding.openRectWalkArc_range_subset
    (E : PeriodicPlaneEmbedding P) {B : ℝ}
    (hB0 : 0 ≤ B)
    (hB : ∀ {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
      |E.coordinates (E.edgeArc hxy t - E.vertex x) i| ≤ B)
    {a b c d : ℝ} {eta : ConfigSpace (Sym2 (E.RectVertex a b c d))}
    {x y : E.RectVertex a b c d}
    (p : (FK.openSub (E.rectGraph a b c d) eta).Walk x y) :
    Set.range (E.walkArc (p.map (E.openRectHom a b c d eta))) ⊆
      E.planeRect (a - B) (b + B) (c - B) (d + B) := by
  apply E.walkArc_range_subset_expanded_planeRect hB0 hB
  intro v hv
  rw [SimpleGraph.Walk.support_map] at hv
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv
  change a ≤ E.vertexCoord w.1 0 ∧ E.vertexCoord w.1 0 ≤ b ∧
    c ≤ E.vertexCoord w.1 1 ∧ E.vertexCoord w.1 1 ≤ d
  exact w.2


end StatMech.FK.PeriodicPlanar
