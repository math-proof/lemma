/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc3_regionclosed.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc2_forcededgeopen.Part2
import Theorem.StatisticalMechanics.Code.Walls.bkm_dccstepopen
open Set
open StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation


namespace StatMech

namespace Walls

variable {d : ℕ}


theorem bc3_rho_edge_cases (ω : ConfigSpace (Sym2 (Site d)))
    (G : Finset (Sym2 (Site d))) {e : Sym2 (Site d)}
    (hopen : removeSite 0 (forceOpenFinset G ω) e = true) :
    (0 : Site d) ∉ e ∧ (e ∈ G ∨ ω e = true) := by
  
  have h0 : (0 : Site d) ∉ e := by
    by_contra h0
    rw [removeSite_apply_of_mem h0] at hopen
    exact (Bool.false_ne_true) hopen
  refine ⟨h0, ?_⟩
  
  rw [removeSite_apply_of_notMem h0] at hopen
  
  by_cases hG : e ∈ G
  · exact Or.inl hG
  · 
    rw [forceOpenFinset_of_notMem hG] at hopen
    exact Or.inr hopen


end Walls
end StatMech
