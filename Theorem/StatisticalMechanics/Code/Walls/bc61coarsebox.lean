/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc61coarsebox.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc60upperlines.Part2
import Theorem.StatisticalMechanics.Code.Walls.bc54coarse
import Theorem.StatisticalMechanics.Code.Percolation.CanonForestCount
import Def.StatisticalMechanics.Code.Walls.bc61coarsebox
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


theorem bc61_mem_boxAround {d L : ℕ} {y x : Site d} :
    x ∈ bc61_boxAround d L y ↔ (x - y) ∈ box d L := by
  classical
  unfold bc61_boxAround
  rw [Set.Finite.mem_toFinset, Set.mem_image]
  constructor
  · rintro ⟨z, hz, rfl⟩; simpa using hz
  · intro h; exact ⟨x - y, h, by ring⟩


theorem bc61_boxAround_zero (d L : ℕ) : bc61_boxAround d L 0 = boxFinsetBK d L := by
  classical
  ext x
  rw [bc61_mem_boxAround, boxFinsetBK, Set.Finite.mem_toFinset]
  simp


theorem bc61_removeBox_le (d L : ℕ) (y : Site d) (ω : ConfigSpace (Sym2 (Site d))) :
    removeSites (bc61_boxAround d L y) ω ≤ ω :=
  daep_removeSites_le _ ω


theorem bc61_connected_of_cut {d L : ℕ} {y : Site d} {ω : ConfigSpace (Sym2 (Site d))}
    {a b : Site d} (h : Connected d (removeSites (bc61_boxAround d L y) ω) a b) :
    Connected d ω a b :=
  connected_mono (bc61_removeBox_le d L y ω) h


theorem bc61_removeBox_apply_of_notMem {d L : ℕ} {y : Site d} {a b : Site d}
    (ha : a ∉ bc61_boxAround d L y) (hb : b ∉ bc61_boxAround d L y)
    (ω : ConfigSpace (Sym2 (Site d))) :
    removeSites (bc61_boxAround d L y) ω s(a, b) = ω s(a, b) := by
  classical
  unfold removeSites
  rw [if_neg]
  rintro ⟨t, ht, htmem⟩
  rw [Sym2.mem_iff] at htmem
  rcases htmem with rfl | rfl
  · exact ha ht
  · exact hb ht


theorem bc61_cut_adj_connected {d L : ℕ} {y : Site d} {a b : Site d}
    {ω : ConfigSpace (Sym2 (Site d))}
    (hadj : (hypercubicLattice d).Adj a b) (hopen : ω s(a, b) = true)
    (ha : a ∉ bc61_boxAround d L y) (hb : b ∉ bc61_boxAround d L y) :
    Connected d (removeSites (bc61_boxAround d L y) ω) a b := by
  refine IsOpenEdge.connected ⟨hadj, ?_⟩
  rw [bc61_removeBox_apply_of_notMem ha hb ω]; exact hopen


end StatMech.Walls
