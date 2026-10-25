/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/pwwbdedge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Lattice.BdEdgeMatchClose
import Theorem.StatisticalMechanics.Code.Walls.kwceventtocut.Part3
import Def.StatisticalMechanics.Code.Walls.pwwbdedge.Part2
open Set SimpleGraph


namespace StatMech

namespace Walls

open StatMech.Lattice


theorem pww_backForth_edge_mem :
    s(pww_a, pww_b) ∈ pww_backForth.edges.toFinset := by
  simp [pww_backForth, SimpleGraph.Walk.edges_cons]


theorem pww_backForth_rayCount_even (z : Site 2) :
    Even (jec_rayCount z pww_backForth) := by
  classical
  
  have hedges : pww_backForth.edges = [s(pww_a, pww_b), s(pww_a, pww_b)] := by
    simp [pww_backForth, SimpleGraph.Walk.edges_cons, Sym2.eq_swap]
  rw [jec_rayCount, hedges]
  
  by_cases h : jec_rayEdge z s(pww_a, pww_b)
  · simp [h]
  · simp [h]


theorem pww_backForth_leftRegion_empty :
    jec_leftRegion pww_backForth = (∅ : Set (Site 2)) := by
  ext z
  simp only [jec_mem_leftRegion, Set.mem_empty_iff_false, iff_false, not_not]
  exact pww_backForth_rayCount_even z


theorem pww_backForth_not_bdEdge :
    ¬ bdEdge (jec_leftRegion pww_backForth) s(pww_a, pww_b) := by
  rw [pww_backForth_leftRegion_empty, bdEdge_mk]
  simp


theorem pww_PrimalWalkLeftRegionMatch_false : ¬ kwc_PrimalWalkLeftRegionMatch := by
  intro h
  
  have := (h pww_backForth pww_a_adj_b).mp pww_backForth_edge_mem
  exact pww_backForth_not_bdEdge this


theorem pww_bdEdge_endpoint_on_support {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {u v : Site 2} (hadj : (hypercubicLattice 2).Adj u v)
    (hbd : bdEdge (jec_leftRegion Vc) s(u, v)) :
    u ∈ Vc.support ∨ v ∈ Vc.support :=
  jec_leftRegion_bdEdge_support Vc hadj hbd


theorem pww_bdEdge_iff_flip_and_support {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {u v : Site 2} (hadj : (hypercubicLattice 2).Adj u v) :
    bdEdge (jec_leftRegion Vc) s(u, v) ↔
      ((u ∈ jec_leftRegion Vc ↔ v ∉ jec_leftRegion Vc) ∧
        (u ∈ Vc.support ∨ v ∈ Vc.support)) :=
  bemc_bdEdge_iff_support_flip Vc hadj


end Walls
end StatMech
