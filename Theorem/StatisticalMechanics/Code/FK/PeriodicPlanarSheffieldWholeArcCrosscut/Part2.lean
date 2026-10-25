/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldWholeArcCrosscut.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.ContinuousRectangleCrossing.Part9
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldHalfPlaneCage.Part9
import Structure.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldWholeArcCrosscut
open Set SimpleGraph Topology
open scoped unitInterval


namespace StatMech

namespace FK.PeriodicPlanar

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}

namespace PeriodicPlanarDualPair

theorem WholeArcBoundaryPlacement.toIncidence_of_exposedEndpoint
    (D : PeriodicPlanarDualPair P Pdual)
    {x y : V} {a b : W}
    {p : P.graph.Walk x y} {q : Pdual.graph.Walk a b}
    (hplace : WholeArcBoundaryPlacement D p q)
    {right bottom top : Real}
    (hcrossRight : ∀ t : unitInterval,
      D.primalEmbedding.coordinates
        (D.primalEmbedding.simpleWalkArc p t) 0 < right)
    (hcrossBottom : ∀ t : unitInterval, bottom <
      D.primalEmbedding.coordinates
        (D.primalEmbedding.simpleWalkArc p t) 1)
    (hcrossTop : ∀ t : unitInterval,
      D.primalEmbedding.coordinates
        (D.primalEmbedding.simpleWalkArc p t) 1 < top)
    (hexit : right < D.dualEmbedding.vertexCoord b 0 ∨
      D.dualEmbedding.vertexCoord b 1 < bottom ∨
      top < D.dualEmbedding.vertexCoord b 1) :
    WholeArcBoundaryIncidence D p q := by
  refine { toWholeArcBoundaryPlacement := hplace
           dual_endpoint_outside := ?_ }
  rcases hexit with hright | hbottom | htop
  · left
    intro t
    exact (hcrossRight t).trans hright
  · right; right
    intro t
    exact hbottom.trans (hcrossBottom t)
  · right; left
    intro t
    exact (hcrossTop t).trans htop


theorem no_open_primal_dual_of_wholeArcBoundaryIncidence
    (D : PeriodicPlanarDualPair P Pdual)
    (omega : ConfigSpace (Sym2 V))
    {x y : V} {a b : W}
    (p : P.graph.Walk x y) (q : Pdual.graph.Walk a b)
    (hp : ¬p.Nil) (hq : ¬q.Nil)
    (hpopen : ∀ {u v : V}, s(u, v) ∈ p.edges ->
      omega s(u, v) = true)
    (hqopen : ∀ {u v : W}, s(u, v) ∈ q.edges ->
      dualConfigEquiv D.edgeDual omega s(u, v) = true)
    (hinc : WholeArcBoundaryIncidence D p q) : False := by
  let pcross := (D.primalEmbedding.simpleWalkArc p).map
    D.primalEmbedding.coordinates.continuous
  let descape := (D.dualEmbedding.simpleWalkArc q).map
    D.dualEmbedding.coordinates.continuous
  obtain ⟨t, s, hts⟩ :=
    ContinuousHalfPlaneCrosscut.wholeArc_intersects_escape_of_outside
      pcross descape hinc.lower_boundary hinc.upper_boundary
        hinc.root_above_lower hinc.root_below_upper
        hinc.primal_in_halfPlane hinc.dual_in_halfPlane
        hinc.dual_endpoint_outside
  have hcoord : D.primalEmbedding.coordinates
      (D.primalEmbedding.simpleWalkArc p t) =
      D.dualEmbedding.coordinates
        (D.dualEmbedding.simpleWalkArc q s) := by
    simpa only [pcross, descape] using hts
  have hphysical : D.primalEmbedding.simpleWalkArc p t =
      D.dualEmbedding.simpleWalkArc q s := by
    rw [← D.coordinates_eq] at hcoord
    exact D.primalEmbedding.coordinates.injective hcoord
  have hdisjoint := D.no_open_primal_dual_simpleWalkArc_crossing
    omega p q hp hq hpopen hqopen
  exact Set.disjoint_left.1 hdisjoint
    ⟨t, rfl⟩ ⟨s, hphysical.symm⟩


end PeriodicPlanarDualPair
end FK.PeriodicPlanar
end StatMech
