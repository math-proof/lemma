/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthStripGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexFiniteStripEnum.Part6
import Theorem.StatisticalMechanics.Code.Universality.HexStripCountsClose.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexAllWidthStripGeometry.Part14


namespace StatMech.Universality

open Complex HexWalk

noncomputable section

def hexAWInteriorPairingOfDomain {T L : ℕ}
    (D : HexDomain (HexAWVertex T L))
    (hpos : ∀ v, D.pos v = hexAWPos v.1)
    (hmid : ∀ v e, D.mid v e = hexAWMid v.1 e) :
    D.InteriorPairing where
  interior := hexAWInteriorIncidences T L
  pair := hexAWPairIncidence
  pair_mem := by
    intro e he
    rw [hexAW_mem_interior_iff] at he ⊢
    rw [hexAWPairIncidence_eq_mate e he]
    exact (hexAWInteriorMate ⟨e, he⟩).2
  pair_invol := by
    intro e he
    rw [hexAW_mem_interior_iff] at he
    have hm : hexAWIsInterior (hexAWInteriorMate ⟨e, he⟩).1 :=
      (hexAWInteriorMate ⟨e, he⟩).2
    rw [hexAWPairIncidence_eq_mate e he,
      hexAWPairIncidence_eq_mate _ hm]
    exact congrArg Subtype.val (hexAWInteriorMate_invol ⟨e, he⟩)
  pair_ne := by
    intro e he
    rw [hexAW_mem_interior_iff] at he
    rw [hexAWPairIncidence_eq_mate e he]
    exact fun h => hexAWInteriorMate_ne ⟨e, he⟩ (Subtype.ext h)
  cancel := by
    intro e he
    rw [hexAW_mem_interior_iff] at he
    rw [hexAWPairIncidence_eq_mate e he]
    unfold HexDomain.incTerm
    simp_rw [hmid, hpos]
    simp only [hexAWInteriorMate_edge, hexAWInteriorMate_vtx]
    have hop := hexAWMid_sub_pos_neighbor e.vtx.1 e.edge
    simp only [hexAWMid_neighbor] at hop
    rw [hexAWMid_neighbor, hop]
    ring


end
end StatMech.Universality
