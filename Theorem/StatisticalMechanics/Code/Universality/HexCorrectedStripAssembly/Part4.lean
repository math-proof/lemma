/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripGeometry.Part11
import Def.StatisticalMechanics.Code.Universality.HexCorrectedStripAssembly.Part4


namespace StatMech.Universality

open Complex HexWalk Set

open scoped BigOperators

noncomputable section

@[simp] theorem hexCSInteriorMate_edge {T L : ℕ}
    (e : HexCSInteriorIncidence T L) :
    (hexCSInteriorMate e).1.edge = e.1.edge := rfl

@[simp] theorem hexCSInteriorMate_vtx {T L : ℕ}
    (e : HexCSInteriorIncidence T L) :
    (hexCSInteriorMate e).1.vtx.1 =
      hexAWNeighbor e.1.vtx.1 e.1.edge := rfl

@[simp] theorem hexCSInteriorMate_invol {T L : ℕ}
    (e : HexCSInteriorIncidence T L) :
    hexCSInteriorMate (hexCSInteriorMate e) = e := by
  apply Subtype.ext
  cases e with
  | mk e he =>
      cases e with
      | mk v edge =>
          rw [HexIncidence.mk.injEq]
          exact ⟨Subtype.ext (hexAWNeighbor_invol v.1 edge), rfl⟩

theorem hexCSInteriorMate_ne {T L : ℕ}
    (e : HexCSInteriorIncidence T L) :
    hexCSInteriorMate e ≠ e := by
  intro h
  have hv : (hexCSInteriorMate e).1.vtx.1 = e.1.vtx.1 :=
    congrArg (fun q => q.1.vtx.1) h
  rw [hexCSInteriorMate_vtx] at hv
  exact hexAWNeighbor_ne e.1.vtx.1 e.1.edge hv

@[simp] theorem hexCSInteriorMate_mid {T L : ℕ}
    (e : HexCSInteriorIncidence T L) :
    hexAWMid (hexCSInteriorMate e).1.vtx.1
        (hexCSInteriorMate e).1.edge =
      hexAWMid e.1.vtx.1 e.1.edge := by
  rw [hexCSInteriorMate_edge, hexCSInteriorMate_vtx, hexAWMid_neighbor]

theorem hexCSInteriorMate_opposite {T L : ℕ}
    (e : HexCSInteriorIncidence T L) :
    hexAWMid (hexCSInteriorMate e).1.vtx.1
          (hexCSInteriorMate e).1.edge -
        hexAWPos (hexCSInteriorMate e).1.vtx.1 =
      -(hexAWMid e.1.vtx.1 e.1.edge - hexAWPos e.1.vtx.1) := by
  rw [hexCSInteriorMate_edge, hexCSInteriorMate_vtx,
    hexAWMid_sub_pos_neighbor]

end
end StatMech.Universality
