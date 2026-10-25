/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bpt2corridors.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bxpxpos.Part3
import Theorem.StatisticalMechanics.Code.Inequalities.DisjointOccurrence.Part3
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerCompression.Part5
import Def.StatisticalMechanics.Code.Walls.bpt2corridors.Part4
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace
open StatMech.Percolation


namespace StatMech.Walls

set_option linter.style.longLine false

set_option linter.unusedVariables false

set_option linter.unusedSectionVars false

set_option maxRecDepth 4000


theorem bpt2_removeSite_closeI_omega :
    removeSite 0 (bpt2_closeI bmf_I bpt2_omega) = removeSite 0 bmf_omegaTri := by
  unfold bpt2_omega
  rw [bpt2_closeI_forceOpen, bpt2_closeI_omegaTri]


theorem bpt2_omega_mem_cylinder :
    bpt2_omega ∈ cylinder bmf_I ({bmf_η₀} : Set (ConfigSpace ↥bmf_I)) := by
  rw [MeasureTheory.mem_cylinder, Set.mem_singleton_iff]
  funext e
  simp only [Finset.restrict, bpt2_omega, bmf_η₀, forceOpenFinset_of_mem e.2]


theorem bpt2_omega_mem_Ext :
    bpt2_omega ∈ bpt2_Ext bmf_I bmf_a₁ bmf_a₂ bmf_a₃ bmf_b₁ bmf_b₂ bmf_b₃ := by
  change bpt2_ExtPred bmf_I bmf_a₁ bmf_a₂ bmf_a₃ bmf_b₁ bmf_b₂ bmf_b₃
    (removeSite 0 (bpt2_closeI bmf_I bpt2_omega))
  rw [bpt2_removeSite_closeI_omega]
  refine ⟨bpt2_S₁, bpt2_S₂, bpt2_S₃,
    ⟨bpt2_a₁_mem_S₁, bpt2_a₂_mem_S₂, bpt2_a₃_mem_S₃⟩,
    ⟨bpt2_x₁_mem_S₁, bpt2_x₂_mem_S₂, bpt2_x₃_mem_S₃⟩,
    ⟨bpt2_disjoint_S₁_S₂, bpt2_disjoint_S₁_S₃, bpt2_disjoint_S₂_S₃⟩,
    ⟨bpt2_I_respects_S₁, bpt2_I_respects_S₂, bpt2_I_respects_S₃⟩,
    ⟨bpt2_S₁_closed, bpt2_S₂_closed, bpt2_S₃_closed⟩,
    ⟨bmf_b₁_cluster_infinite, bmf_b₂_cluster_infinite, bmf_b₃_cluster_infinite⟩⟩


theorem bpt2_omega_mem_precursor :
    bpt2_omega ∈ NeighborTrifPrecursor 2 bmf_a₁ bmf_a₂ bmf_a₃ :=
  bpt2_hgeo bmf_I bmf_a₁ bmf_a₂ bmf_a₃ bmf_b₁ bmf_b₂ bmf_b₃ bmf_η₀
    ⟨bmf_a₁_ne_a₂, bmf_a₁_ne_a₃, bmf_a₂_ne_a₃⟩
    ⟨bmf_adj_o_a₁, bmf_adj_o_a₂, bmf_adj_o_a₃⟩
    (fun ω hω => ⟨bmf_conn_a₁_b₁ ω hω, bmf_conn_a₂_b₂ ω hω, bmf_conn_a₃_b₃ ω hω⟩)
    ⟨bpt2_omega_mem_cylinder, bpt2_omega_mem_Ext⟩


theorem bpt2_Ext_nonempty :
    (bpt2_Ext bmf_I bmf_a₁ bmf_a₂ bmf_a₃ bmf_b₁ bmf_b₂ bmf_b₃).Nonempty :=
  ⟨bpt2_omega, bpt2_omega_mem_Ext⟩

end StatMech.Walls
