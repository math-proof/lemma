/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/DualCircuitToWalk.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.RSW.Defs.Part7
import Theorem.StatisticalMechanics.Code.RSW.SelfDuality.Part2
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Lattice.FaceRegion.Part3
import Theorem.StatisticalMechanics.Code.Lattice.JordanContour.Part3
import Theorem.StatisticalMechanics.Code.Universality.BoxCrossingDichotomy
import Def.StatisticalMechanics.Code.Universality.DualCircuitToWalk
open Set SimpleGraph
open StatMech.Lattice
open StatMech.RSW.Box


namespace StatMech

namespace Universality

variable {ω : ConfigSpace (Sym2 (Site 2))} {n : ℤ}


theorem dcw_barrier_closed (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) {v w : Site 2}
    (h : dcw_isBarrierEdge ω n v w) : ω s(v, w) = false :=
  bcd_leftReach_boundary_closed ω n h.1 h.2.1 h.2.2.2 h.2.2.1


theorem dcw_barrier_dual_open (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) {v w : Site 2}
    (h : dcw_isBarrierEdge ω n v w) : dualConfig ω (crossEdge s(v, w)) = true :=
  bcd_leftReach_boundary_dual_open ω n h.1 h.2.1 h.2.2.2 h.2.2.1


theorem dcw_barrier_dualAdj (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) {v w : Site 2}
    (h : dcw_isBarrierEdge ω n v w) :
    (openSubgraph 2 (dualConfig ω)).Adj (rot90Fun v) (rot90Fun w) := by
  refine ⟨?_, ?_⟩
  · exact (rot90_adj v w).mpr h.2.2.2
  · have := dcw_barrier_dual_open ω n h
    rwa [crossEdge_mk] at this


theorem dcw_leftSide_in_L (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    {x : Site 2} (hx : x ∈ leftSide 0 n 0 n) :
    x ∈ bcd_leftReach ω n := by
  refine ⟨leftSide_subset hx, x, hx, leftSide_subset hx, ?_⟩
  exact connectedWithin_refl ω (rect 0 n 0 n) ⟨x, leftSide_subset hx⟩

theorem dcw_rightSide_notin_L (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (hnoH : ¬ HorizontalCrossing ω 0 n 0 n) {y : Site 2} (hy : y ∈ rightSide 0 n 0 n) :
    y ∉ bcd_leftReach ω n :=
  (bcd_no_horizontal_iff_right_unreachable ω n).mp hnoH y hy


theorem dcw_barrier_separates (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (hnoH : ¬ HorizontalCrossing ω 0 n 0 n)
    {x y : Site 2} (hx : x ∈ leftSide 0 n 0 n) (hy : y ∈ rightSide 0 n 0 n) :
    ¬ (latticeMinusBarrier (bcd_leftReach ω n)).Reachable x y :=
  not_reachable_latticeMinusBarrier (bcd_leftReach ω n)
    (dcw_leftSide_in_L ω n hx) (dcw_rightSide_notin_L ω n hnoH hy)


theorem dcw_leftRight_crossCount_odd (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (hnoH : ¬ HorizontalCrossing ω 0 n 0 n)
    {x y : Site 2} (hx : x ∈ leftSide 0 n 0 n) (hy : y ∈ rightSide 0 n 0 n)
    (w : (hypercubicLattice 2).Walk x y) :
    ¬ Even (crossCount (bcd_leftReach ω n) w) := by
  rw [crossCount_parity]
  intro hiff
  exact dcw_rightSide_notin_L ω n hnoH hy (hiff.mp (dcw_leftSide_in_L ω n hx))


theorem dcw_primal_blocks_dual (ω : ConfigSpace (Sym2 (Site 2)))
    {x y : Site 2} (w : (openSubgraph 2 ω).Walk x y)
    {x' y' : Site 2} (w' : (openSubgraph 2 (dualConfig ω)).Walk x' y')
    (e : Sym2 (Site 2)) (he : e ∈ w.edges) (he' : crossEdge e ∈ w'.edges) :
    False :=
  StatMech.RSW.openWalk_blocks_dualWalk ω w w' e he he'


end Universality
end StatMech
