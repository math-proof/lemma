/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldWholeArcCrosscut.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.ContinuousRectangleCrossing.Part9
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldHalfPlaneCage.Part9
import Structure.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldWholeArcCrosscut.Part2
open Set SimpleGraph Topology
open scoped unitInterval


namespace StatMech

namespace FK.PeriodicPlanar

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}

namespace PeriodicPlanarDualPair

theorem no_open_primal_dual_of_wholeArcTraceIncidence
    (D : PeriodicPlanarDualPair P Pdual)
    (omega : ConfigSpace (Sym2 V))
    {x y : V} {a b : W}
    (p : P.graph.Walk x y) (q : Pdual.graph.Walk a b)
    (hp : ¬p.Nil) (hq : ¬q.Nil)
    (hpopen : ∀ {u v : V}, s(u, v) ∈ p.edges ->
      omega s(u, v) = true)
    (hqopen : ∀ {u v : W}, s(u, v) ∈ q.edges ->
      dualConfigEquiv D.edgeDual omega s(u, v) = true)
    (hinc : WholeArcTraceIncidence D p q) : False := by
  obtain ⟨t, s, hts⟩ :=
    ContinuousHalfPlaneCrosscut.wholeArc_intersects_escape_of_outside
      hinc.primalTrace hinc.dualTrace
        hinc.lower_boundary hinc.upper_boundary
        hinc.root_above_lower hinc.root_below_upper
        hinc.primal_in_halfPlane hinc.dual_in_halfPlane
        hinc.dual_endpoint_outside
  have hpMem := hinc.primal_range ⟨t, rfl⟩
  have hqMem := hinc.dual_range ⟨s, rfl⟩
  obtain ⟨tp, htp⟩ := hpMem
  obtain ⟨tq, htq⟩ := hqMem
  have hcoord : D.primalEmbedding.coordinates
      (D.primalEmbedding.simpleWalkArc p tp) =
      D.dualEmbedding.coordinates
        (D.dualEmbedding.simpleWalkArc q tq) := by
    exact htp.trans (hts.trans htq.symm)
  have hphysical : D.primalEmbedding.simpleWalkArc p tp =
      D.dualEmbedding.simpleWalkArc q tq := by
    rw [← D.coordinates_eq] at hcoord
    exact D.primalEmbedding.coordinates.injective hcoord
  have hdisjoint := D.no_open_primal_dual_simpleWalkArc_crossing
    omega p q hp hq hpopen hqopen
  exact Set.disjoint_left.1 hdisjoint
    ⟨tp, rfl⟩ ⟨tq, hphysical.symm⟩

end PeriodicPlanarDualPair
end FK.PeriodicPlanar
end StatMech
