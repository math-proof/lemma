/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRightStripConnection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectInducedConditionalLower.Part3
import Theorem.StatisticalMechanics.Code.FK.FKG
import Theorem.StatisticalMechanics.Code.FK.TwoPoint.Part4
import Abbrev.StatisticalMechanics.Code.FrontierD.FKRectRightStripConnection


namespace StatMech.FrontierD

noncomputable section

theorem fkRect_innerEdge_subtype_mk_mem_range_iff
    (R : FKRectTorus) (S : Set R.Vertex) (x y : R.Vertex) :
    s(x, y) ∈ Set.range (FK.ocd_innerEdge
      (Subtype.val : FKRectInducedVertex R S → R.Vertex)) ↔
      x ∈ S ∧ y ∈ S := by
  constructor
  · rintro ⟨e, he⟩
    induction e using Sym2.ind with
    | _ u v =>
        rw [FK.ocd_innerEdge_mk, Sym2.eq_iff] at he
        rcases he with he | he
        · exact ⟨he.1 ▸ u.2, he.2 ▸ v.2⟩
        · exact ⟨he.2 ▸ v.2, he.1 ▸ u.2⟩
  · rintro ⟨hx, hy⟩
    exact ⟨s(⟨x, hx⟩, ⟨y, hy⟩), by rw [FK.ocd_innerEdge_mk]⟩


theorem fkRect_verticalSeam_not_innerEdgeRange_of_rowZero_disjoint
    (R : FKRectTorus) (S : Set R.Vertex)
    (hzero : ∀ v ∈ S, v.2.val ≠ 0)
    {e : Sym2 R.Vertex} (he : fkRectCrossesVerticalSeam R e) :
    e ∉ Set.range (FK.ocd_innerEdge
      (Subtype.val : FKRectInducedVertex R S → R.Vertex)) := by
  induction e using Sym2.ind with
  | _ x y =>
      intro hrange
      have hxy := (fkRect_innerEdge_subtype_mk_mem_range_iff R S x y).1
        hrange
      rw [fkRectCrossesVerticalSeam_mk] at he
      rcases he with he | he
      · exact hzero x hxy.1 he.1
      · exact hzero y hxy.2 he.1

theorem fkRect_verticalSeam_not_rightStripBand_innerEdgeRange
    (R : FKRectTorus) (cut lower upper : Nat) (hlower : 1 ≤ lower)
    {e : Sym2 R.Vertex} (he : fkRectCrossesVerticalSeam R e) :
    e ∉ Set.range (FK.ocd_innerEdge
      (Subtype.val : FKRectRightStripBandVertex R cut lower upper →
        R.Vertex)) := by
  apply fkRect_verticalSeam_not_innerEdgeRange_of_rowZero_disjoint R
    (fkRectRightStripBand R cut lower upper) _ he
  intro v hv
  exact Nat.ne_of_gt (Nat.zero_lt_one.trans_le
    (hlower.trans hv.2.1))


end
end StatMech.FrontierD
