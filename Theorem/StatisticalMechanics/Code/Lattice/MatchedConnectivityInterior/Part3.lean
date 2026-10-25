/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/MatchedConnectivityInterior.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Lattice.JordanInteriorLib.Part4
import Theorem.StatisticalMechanics.Code.Lattice.InteriorWindingClose
import Theorem.StatisticalMechanics.Code.Lattice.SegmentDownClose.Part2
import Def.StatisticalMechanics.Code.Lattice.MatchedConnectivityInterior.Part3
open Set SimpleGraph Function


namespace StatMech

namespace Lattice

theorem mci_fjord_no_row1_horizontal_edge :
    s((![3, 1] : Site 2), (![4, 1] : Site 2)) ∉ sdc_fjord.edges := by
  intro hedge
  unfold sdc_fjord at hedge
  simp only [SimpleGraph.Walk.edges_append, SimpleGraph.Walk.edges_copy,
    SimpleGraph.Walk.edges_reverse, List.mem_append, List.mem_reverse] at hedge
  
  
  rcases hedge with h|h|h|h|h|h|h|h
  · 
    have := (mci_hseg_edge_row 0 0 3 h).1; simp at this
  · 
    have := (mci_vseg_edge_col 3 0 3 h).2; simp at this
  · 
    have := (mci_hseg_edge_row 3 3 1 h).1; simp at this
  · 
    have := (mci_vseg_edge_col 4 0 3 h).1; simp at this
  · 
    have := (mci_hseg_edge_row 0 4 3 h).1; simp at this
  · 
    have := (mci_vseg_edge_col 7 0 4 h).1; simp at this
  · 
    have := (mci_hseg_edge_row 4 0 7 h).1; simp at this
  · 
    have := (mci_vseg_edge_col 0 0 4 h).1; simp at this


theorem mci_fjord_on_31 : (![3, 1] : Site 2) ∈ sdc_fjord.support := by
  unfold sdc_fjord
  simp only [SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.support_copy,
    SimpleGraph.Walk.support_reverse, List.mem_reverse]
  right; left
  exact sdc_vsegUp_mem' 3 0 3 1 (by norm_num) (by norm_num)


theorem mci_fjord_not_fourThin : ¬ mci_FourThin sdc_fjord := by
  intro hthin
  have hadj : (hypercubicLattice 2).Adj (![3, 1] : Site 2) ![4, 1] := by
    rw [hypercubicLattice_adj, Fin.sum_univ_two]; decide
  exact mci_fjord_no_row1_horizontal_edge (hthin _ _ mci_fjord_on_31 sdc_fjord_on_41 hadj)


theorem mci_fjord_pockets_not_king_adjacent :
    ¬ mci_kingGraph.Adj (![2, 1] : Site 2) (![5, 1] : Site 2) := by
  rw [mci_kingGraph_adj]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, not_and]
  intro h; omega


end Lattice
end StatMech
