/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectLocalBoxEmbedding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDevelopedSquare.Part11
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRightStripConnection.Part3
import Theorem.StatisticalMechanics.Code.FK.FKGeneralQConnectionSymmetry
open MeasureTheory StatMech.Lattice StatMech.Percolation SimpleGraph


namespace StatMech.FrontierD

noncomputable section

theorem hypercubicLattice_two_adj_add_left (a x y : Site 2) :
    (hypercubicLattice 2).Adj (a + x) (a + y) ↔
      (hypercubicLattice 2).Adj x y := by
  rw [hypercubicLattice_adj, hypercubicLattice_adj]
  have hsum :
      (∑ i, ((a + x) i - (a + y) i).natAbs) =
        ∑ i, (x i - y i).natAbs := by
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    simp only [Pi.add_apply]
    ring
  rw [hsum]


theorem fkRectCutGraph_adj_of_torusAdj_of_pos
    (R : FKRectTorus) (x y : R.Vertex)
    (hxcol : 0 < x.1.val) (hycol : 0 < y.1.val)
    (hxrow : 0 < x.2.val) (hyrow : 0 < y.2.val)
    (hxy : (fkRectTorusGraph R).Adj x y) :
    (fkRectCutGraph R).Adj x y := by
  apply (fkRectCutGraph_adj_iff R x y).2
  refine ⟨hxy, ?_⟩
  intro hcut
  rw [fkRectTorusCutGraphEdges, Finset.mem_image] at hcut
  obtain ⟨a, ha, hedge⟩ := hcut
  rw [mem_fkRectTorusCutEdges_iff] at ha
  rcases a with ⟨b, col, row⟩
  rcases ha with hrow | ⟨hb, hcol⟩
  · change row.val = 0 at hrow
    have hzero : row.val = 0 := hrow
    cases b with
    | false =>
      simp only [fkRectTorusIndexedEdge, Bool.false_eq_true, if_false] at hedge
      by_cases heven : Even row.val
      · simp only [heven, if_true] at hedge
        rcases Sym2.eq_iff.mp hedge with h | h
        · exact hxrow.ne' (congrArg (fun v => v.2.val) h.1.symm |>.trans hzero)
        · exact hyrow.ne' (congrArg (fun v => v.2.val) h.1.symm |>.trans hzero)
      · simp only [heven, if_false] at hedge
        rcases Sym2.eq_iff.mp hedge with h | h
        · exact hxrow.ne' (congrArg (fun v => v.2.val) h.1.symm |>.trans hzero)
        · exact hyrow.ne' (congrArg (fun v => v.2.val) h.1.symm |>.trans hzero)
    | true =>
      simp only [fkRectTorusIndexedEdge, if_true] at hedge
      rcases Sym2.eq_iff.mp hedge with h | h
      · exact hxrow.ne' (congrArg (fun v => v.2.val) h.1.symm |>.trans hzero)
      · exact hyrow.ne' (congrArg (fun v => v.2.val) h.1.symm |>.trans hzero)
  · change b = false at hb
    change col.val = 0 at hcol
    subst b
    have hzero : col.val = 0 := hcol
    simp only [fkRectTorusIndexedEdge, Bool.false_eq_true, if_false] at hedge
    by_cases heven : Even row.val
    · simp only [heven, if_true] at hedge
      rcases Sym2.eq_iff.mp hedge with h | h
      · exact hxcol.ne' (congrArg (fun v => v.1.val) h.1.symm |>.trans hzero)
      · exact hycol.ne' (congrArg (fun v => v.1.val) h.1.symm |>.trans hzero)
    · simp only [heven, if_false] at hedge
      rcases Sym2.eq_iff.mp hedge with h | h
      · exact hycol.ne' (congrArg (fun v => v.1.val) h.2.symm |>.trans hzero)
      · exact hxcol.ne' (congrArg (fun v => v.1.val) h.2.symm |>.trans hzero)


end
end StatMech.FrontierD
