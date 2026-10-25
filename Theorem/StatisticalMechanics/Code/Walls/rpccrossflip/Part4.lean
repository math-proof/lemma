/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rpccrossflip.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Lattice.OrbitWindingWitness.Part2
import Theorem.StatisticalMechanics.Code.Lattice.WindingWitness.Part4
import Theorem.StatisticalMechanics.Code.Walls.kwceventtocut.Part3
import Def.StatisticalMechanics.Code.Walls.rpccrossflip.Part4
open Set SimpleGraph
open scoped BigOperators


namespace StatMech

namespace Walls

open StatMech.Lattice


theorem rpc_leftRegion_bdEdge_iff {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (hbridge : rpc_CrossEdgeOddIffOnWalk Vc)
    {u v : Site 2} (hadj : (hypercubicLattice 2).Adj u v) :
    bdEdge (jec_leftRegion Vc) s(u, v) ↔ s(u, v) ∈ Vc.edges := by
  rw [rpc_crossFlip Vc hadj]
  exact hbridge hadj


theorem rpc_primalWalkLeftRegionMatch_of_bridge
    (hbridge : ∀ {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a),
      rpc_CrossEdgeOddIffOnWalk Vc) :
    kwc_PrimalWalkLeftRegionMatch := by
  intro a Vc u v hadj
  rw [List.mem_toFinset]
  exact ((rpc_leftRegion_bdEdge_iff Vc (hbridge Vc) hadj).symm)


theorem rpc_unitSquare_flip :
    bdEdge (jec_leftRegion wwit_unitSquareLoop) s((![0, 1] : Site 2), (![1, 1] : Site 2)) := by
  rw [bdEdge_mk, jec_mem_leftRegion, jec_mem_leftRegion]
  
  have hodd : ¬ Even (jec_rayCount (![1, 1] : Site 2) wwit_unitSquareLoop) :=
    wwit_unitSquareLoop_inside_odd
  have heven : Even (jec_rayCount (![0, 1] : Site 2) wwit_unitSquareLoop) := by
    have hcount : jec_rayCount (![0, 1] : Site 2) wwit_unitSquareLoop = 0 := by
      unfold wwit_unitSquareLoop
      simp only [jec_rayCount_append, jec_rayCount_copy, jec_rayCount_reverse,
        jec_rayCount_vsegUp, jec_rayCount_hsegRight, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one]
      norm_num
    rw [hcount]; exact ⟨0, rfl⟩
  
  simp only [heven, not_true, hodd, not_false_iff]


theorem rpc_unitSquare_crossEdge_odd :
    Odd (wwit_unitSquareLoop.edges.count
      (rpc_crossEdge (![0, 1] : Site 2) (![1, 1] : Site 2))) := by
  have hadj : (hypercubicLattice 2).Adj (![0, 1] : Site 2) (![1, 1] : Site 2) := by
    simp [hypercubicLattice_adj, Fin.sum_univ_two]
  exact (rpc_crossFlip wwit_unitSquareLoop hadj).mp rpc_unitSquare_flip

end Walls
end StatMech
