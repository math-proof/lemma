/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthStripGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexFiniteStripEnum.Part6
import Theorem.StatisticalMechanics.Code.Universality.HexStripCountsClose.Part3
import Def.StatisticalMechanics.Code.Universality.HexAllWidthStripGeometry.Part14


namespace StatMech.Universality

open Complex HexWalk

noncomputable section

@[simp] theorem hexAWInteriorMate_edge {T L : ℕ}
    (e : HexAWInteriorIncidence T L) :
    (hexAWInteriorMate e).1.edge = e.1.edge := rfl

@[simp] theorem hexAWInteriorMate_vtx {T L : ℕ}
    (e : HexAWInteriorIncidence T L) :
    (hexAWInteriorMate e).1.vtx.1 =
      hexAWNeighbor e.1.vtx.1 e.1.edge := rfl


@[simp] theorem hexAWInteriorMate_invol {T L : ℕ}
    (e : HexAWInteriorIncidence T L) :
    hexAWInteriorMate (hexAWInteriorMate e) = e := by
  apply Subtype.ext
  cases e with
  | mk e he =>
    cases e with
    | mk v edge =>
      rw [HexIncidence.mk.injEq]
      constructor
      · apply Subtype.ext
        exact hexAWNeighbor_invol v.1 edge
      · rfl


theorem hexAWInteriorMate_ne {T L : ℕ}
    (e : HexAWInteriorIncidence T L) :
    hexAWInteriorMate e ≠ e := by
  intro h
  have hv : (hexAWInteriorMate e).1.vtx.1 = e.1.vtx.1 :=
    congrArg (fun q => q.1.vtx.1) h
  rw [hexAWInteriorMate_vtx] at hv
  exact hexAWNeighbor_ne e.1.vtx.1 e.1.edge hv


@[simp] theorem hexAWInteriorMate_mid {T L : ℕ}
    (e : HexAWInteriorIncidence T L) :
    hexAWMid (hexAWInteriorMate e).1.vtx.1
        (hexAWInteriorMate e).1.edge =
      hexAWMid e.1.vtx.1 e.1.edge := by
  rw [hexAWInteriorMate_edge, hexAWInteriorMate_vtx,
    hexAWMid_neighbor]


theorem hexAWInteriorMate_opposite {T L : ℕ}
    (e : HexAWInteriorIncidence T L) :
    hexAWMid (hexAWInteriorMate e).1.vtx.1
          (hexAWInteriorMate e).1.edge -
        hexAWPos (hexAWInteriorMate e).1.vtx.1 =
      -(hexAWMid e.1.vtx.1 e.1.edge - hexAWPos e.1.vtx.1) := by
  rw [hexAWInteriorMate_edge, hexAWInteriorMate_vtx,
    hexAWMid_sub_pos_neighbor]


end
end StatMech.Universality
