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
import Def.StatisticalMechanics.Code.Walls.rpccrossflip.Part3
open Set SimpleGraph
open scoped BigOperators


namespace StatMech

namespace Walls

open StatMech.Lattice


theorem rpc_crossFlip {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {u v : Site 2} (hadj : (hypercubicLattice 2).Adj u v) :
    bdEdge (jec_leftRegion Vc) s(u, v) ↔ Odd (Vc.edges.count (rpc_crossEdge u v)) := by
  have hadj' := hadj
  rw [hypercubicLattice_adj, Fin.sum_univ_two] at hadj'
  rw [bdEdge_mk, jec_mem_leftRegion, jec_mem_leftRegion]
  
  have hrestate : ((¬ Even (jec_rayCount u Vc)) ↔ ¬ ¬ Even (jec_rayCount v Vc)) ↔
      (Even (jec_rayCount u Vc) ↔ ¬ Even (jec_rayCount v Vc)) := by
    constructor <;> intro h <;>
      · by_cases hu : Even (jec_rayCount u Vc) <;> by_cases hv : Even (jec_rayCount v Vc) <;>
          simp_all
  rw [hrestate, rpc_crossEdge]
  by_cases hc0 : v 0 = u 0 + 1
  · rw [if_pos hc0]; exact rpc_horizontalFlip_iff Vc u v hc0 (by omega)
  · rw [if_neg hc0]
    by_cases hc0' : u 0 = v 0 + 1
    · rw [if_pos hc0']
      have hfl := rpc_horizontalFlip_iff Vc v u hc0' (by omega)
      rw [← hfl]
      constructor <;> intro h <;>
        · by_cases hu : Even (jec_rayCount u Vc) <;> by_cases hv : Even (jec_rayCount v Vc) <;>
            simp_all
    · rw [if_neg hc0']
      
      have hv0 : v 0 = u 0 := by omega
      by_cases hc1 : v 1 = u 1 + 1
      · rw [if_pos hc1]; exact rpc_verticalFlip_iff Vc u v hv0 hc1
      · rw [if_neg hc1]
        have hc1' : u 1 = v 1 + 1 := by omega
        have hfl := rpc_verticalFlip_iff Vc v u (by omega) hc1'
        rw [← hfl]
        constructor <;> intro h <;>
          · by_cases hu : Even (jec_rayCount u Vc) <;> by_cases hv : Even (jec_rayCount v Vc) <;>
              simp_all


end Walls
end StatMech
