/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc64coarseembed.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc63coarseforest.Part2
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


theorem bc64_boxAround_disjoint_of_farCoord {L : ℕ} {y y' : Site d} (i : Fin d)
    (hfar : 2 * L < ((y - y') i).natAbs) :
    Disjoint (bc61_boxAround d L y) (bc61_boxAround d L y') := by
  classical
  rw [Finset.disjoint_left]
  intro x hx hx'
  rw [bc61_mem_boxAround, mem_box] at hx hx'
  have h1 : ((x - y) i).natAbs ≤ L := hx i
  have h2 : ((x - y') i).natAbs ≤ L := hx' i
  
  have hsub : (y - y') i = (x - y') i - (x - y) i := by
    simp only [Pi.sub_apply]; ring
  have hle : ((y - y') i).natAbs ≤ ((x - y') i).natAbs + ((x - y) i).natAbs := by
    rw [hsub]; exact Int.natAbs_sub_le _ _
  omega


theorem bc64_boxAround_disjoint_of_far {L : ℕ} {y y' : Site d}
    (hfar : ∃ i, 2 * L < ((y - y') i).natAbs) :
    Disjoint (bc61_boxAround d L y) (bc61_boxAround d L y') := by
  obtain ⟨i, hi⟩ := hfar
  exact bc64_boxAround_disjoint_of_farCoord i hi


theorem bc64_notMem_both_of_far {L : ℕ} {y y' x : Site d} (i : Fin d)
    (hfar : 2 * L < ((y - y') i).natAbs)
    (hx : x ∈ bc61_boxAround d L y) : x ∉ bc61_boxAround d L y' := by
  intro hx'
  exact (Finset.disjoint_left.mp (bc64_boxAround_disjoint_of_farCoord i hfar) hx) hx'


end StatMech.Walls
