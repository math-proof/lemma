/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc_leafremoval.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.EarContraction.Part9
import Def.StatisticalMechanics.Code.Walls.jc_leafremoval.Part2
open SimpleGraph


namespace StatMech

namespace Walls

open StatMech.Lattice


theorem jc_mem_domino (v : Site 2) : v ∈ jc_domino ↔ v = ![0, 0] ∨ v = ![1, 0] := by
  unfold jc_domino; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]

theorem jc_domino_00 : (![0, 0] : Site 2) ∈ jc_domino := by rw [jc_mem_domino]; tauto

theorem jc_domino_10 : (![1, 0] : Site 2) ∈ jc_domino := by rw [jc_mem_domino]; tauto


theorem jc_domino_cellConnected : CellConnected jc_domino := by
  rw [CellConnected, SimpleGraph.connected_iff]
  refine ⟨?_, ⟨⟨![0, 0], jc_domino_00⟩⟩⟩
  have e : ((hypercubicLattice 2).induce jc_domino).Adj ⟨![0, 0], jc_domino_00⟩
      ⟨![1, 0], jc_domino_10⟩ := by
    rw [SimpleGraph.induce_adj, hypercubicLattice_adj, Fin.sum_univ_two]; norm_num
  have r0 : ∀ x : ↑jc_domino,
      ((hypercubicLattice 2).induce jc_domino).Reachable ⟨![0, 0], jc_domino_00⟩ x := by
    rintro ⟨x, hx⟩
    rw [jc_mem_domino] at hx
    rcases hx with h | h <;> subst h
    · rfl
    · exact e.reachable
  intro a b
  exact (r0 a).symm.trans (r0 b)


theorem jc_domino_pendant_origin : jc_IsPendantCell jc_domino ![0, 0] := by
  refine ⟨jc_domino_00, ![1, 0], ⟨jc_domino_10, ?_⟩, ?_⟩
  · rw [hypercubicLattice_adj, Fin.sum_univ_two]; norm_num
  · rintro w ⟨hwd, hadj⟩
    rw [jc_mem_domino] at hwd
    rcases hwd with h | h
    · subst h; rw [hypercubicLattice_adj, Fin.sum_univ_two] at hadj; norm_num at hadj
    · exact h


theorem jc_domino_leaf_removal : CellConnected (jc_domino \ {![0, 0]}) :=
  jc_cellConnected_diff_of_pendant jc_domino ![0, 0] jc_domino_cellConnected
    jc_domino_pendant_origin

end Walls
end StatMech
