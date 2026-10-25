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
import Def.StatisticalMechanics.Code.Lattice.MatchedConnectivityInterior.Part2
open Set SimpleGraph Function


namespace StatMech

namespace Lattice

@[simp] theorem mci_kingGraph_adj (u v : Site 2) :
    mci_kingGraph.Adj u v ↔
      (u 0 - v 0).natAbs ≤ 1 ∧ (u 1 - v 1).natAbs ≤ 1 ∧ u ≠ v := Iff.rfl


theorem mci_hyper_le_king : hypercubicLattice 2 ≤ mci_kingGraph := by
  intro u v hadj
  rw [hypercubicLattice_adj, Fin.sum_univ_two] at hadj
  refine ⟨by omega, by omega, ?_⟩
  intro h; rw [h] at hadj; simp at hadj


theorem mci_kingReachable_of_hyperReachable {u v : Site 2}
    (h : (hypercubicLattice 2).Reachable u v) : mci_kingGraph.Reachable u v :=
  h.mono mci_hyper_le_king


theorem mci_kingAdj_diag (x y : ℤ) (sx sy : ℤ) (hsx : sx = 1 ∨ sx = -1)
    (hsy : sy = 1 ∨ sy = -1) :
    mci_kingGraph.Adj (![x, y] : Site 2) ![x + sx, y + sy] := by
  refine ⟨by simp; omega, by simp; omega, ?_⟩
  intro h
  have := congrFun h 0
  simp only [Matrix.cons_val_zero] at this; omega


theorem mci_vseg_edge_col (col r : ℤ) (k : ℕ) {u v : Site 2}
    (he : s(u, v) ∈ (jec_vsegUp col r k).edges) : u 0 = col ∧ v 0 = col :=
  ⟨(jec_vsegUp_support col r k ((jec_vsegUp col r k).fst_mem_support_of_mem_edges he)).1,
   (jec_vsegUp_support col r k ((jec_vsegUp col r k).snd_mem_support_of_mem_edges he)).1⟩


theorem mci_hseg_edge_row (row t : ℤ) (k : ℕ) {u v : Site 2}
    (he : s(u, v) ∈ (jec_hsegRight row t k).edges) : u 1 = row ∧ v 1 = row :=
  ⟨(jec_hsegRight_support row t k ((jec_hsegRight row t k).fst_mem_support_of_mem_edges he)).1,
   (jec_hsegRight_support row t k ((jec_hsegRight row t k).snd_mem_support_of_mem_edges he)).1⟩


end Lattice
end StatMech
