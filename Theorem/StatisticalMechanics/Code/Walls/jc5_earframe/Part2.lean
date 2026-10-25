/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc5_earframe.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.jc2_runframe.Part2
import Theorem.StatisticalMechanics.Code.Walls.jc2_thickshelf.Part3
import Theorem.StatisticalMechanics.Code.Walls.jc3_shelfcell
import Def.StatisticalMechanics.Code.Walls.jc5_earframe.Part2
open SimpleGraph Function


namespace StatMech

namespace Walls

open StatMech.Lattice


theorem jc5_earUp_eq (c : Site 2) (len : ℤ) :
    jc5_earUp c len = c + ![len, 1] := by
  unfold jc5_earUp jc5_earCell
  funext i; fin_cases i <;> · simp only [Pi.add_apply]; simp


theorem jc5_earRight_eq (c : Site 2) (len : ℤ) :
    jc5_earRight c len = c + ![len + 1, 0] := by
  unfold jc5_earRight jc5_earCell
  funext i; fin_cases i <;> · simp only [Pi.add_apply]; simp; try ring


theorem jc5_earShelf_eq (c : Site 2) (len : ℤ) :
    jc5_earShelf c len = c + ![len, -1] := by
  unfold jc5_earShelf jc5_earCell
  funext i; fin_cases i <;> · simp only [Pi.add_apply]; simp


theorem jc5_earShelf_eq_downCell (c : Site 2) (len : ℤ) :
    jc5_earShelf c len = jc3_downCell c len := by
  rw [jc5_earShelf_eq, jc3_downCell_eq]


theorem jc5_earUp_nmem (K : Set (Site 2)) (c : Site 2) (len : ℤ)
    (hframe : jc2_RunFrame K c len) : jc5_earUp c len ∉ K := by
  rw [jc5_earUp_eq]
  exact hframe.no_up len


theorem jc5_earRight_nmem (K : Set (Site 2)) (c : Site 2) (len : ℤ)
    (hframe : jc2_RunFrame K c len) : jc5_earRight c len ∉ K := by
  rw [jc5_earRight_eq]
  exact hframe.right_out


theorem jc5_earShelf_mem (K : Set (Site 2)) (c : Site 2) (len : ℤ)
    (hthick : jc2_FullyThick K c len) (hlen : 0 ≤ len) : jc5_earShelf c len ∈ K := by
  rw [jc5_earShelf_eq_downCell]
  exact jc3_downCell_mem K c len hthick hlen


theorem jc5_earShelf_ne_ear (c : Site 2) (len : ℤ) :
    jc5_earShelf c len ≠ jc5_earCell c len := by
  rw [jc5_earShelf_eq_downCell, jc5_earCell_eq_runRightEnd]
  exact jc3_downCell_ne_runRightEnd c len


theorem jc5_earShelf_mem_diff (K : Set (Site 2)) (c : Site 2) (len : ℤ)
    (hthick : jc2_FullyThick K c len) (hlen : 0 ≤ len) :
    jc5_earShelf c len ∈ K \ {jc5_earCell c len} :=
  ⟨jc5_earShelf_mem K c len hthick hlen,
   by simpa only [Set.mem_singleton_iff] using jc5_earShelf_ne_ear c len⟩


theorem jc5_earShelf_adj_ear (c : Site 2) (len : ℤ) :
    (hypercubicLattice 2).Adj (jc5_earCell c len) (jc5_earShelf c len) := by
  rw [jc5_earCell_eq_runRightEnd, jc5_earShelf_eq_downCell]
  exact jc3_downCell_adj_runRightEnd c len


end Walls
end StatMech
