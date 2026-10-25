/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthStripGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexFiniteStripEnum.Part6
import Theorem.StatisticalMechanics.Code.Universality.HexStripCountsClose.Part3
import Def.StatisticalMechanics.Code.Universality.HexAllWidthStripGeometry.Part17


namespace StatMech.Universality

open Complex HexWalk

noncomputable section

@[simp] theorem hexAWStartIncidence_mid (T L : ℕ) (hT : 0 < T) :
    hexAWMid (hexAWStartIncidence T L hT).vtx.1
        (hexAWStartIncidence T L hT).edge = hexAWStart :=
  hexAWMid_origin_zero

@[simp] theorem hexAWStartIncidence_heading (T L : ℕ) (hT : 0 < T) :
    hexAWHeading (hexAWStartIncidence T L hT).vtx.1
        (hexAWStartIncidence T L hT).edge = 4 := rfl


theorem hexAWStartIncidence_mem_boundary (T L : ℕ) (hT : 0 < T) :
    hexAWStartIncidence T L hT ∈ hexAWBoundaryIncidences T L := by
  rw [hexAW_mem_boundary_iff]
  unfold hexAWIsInterior hexAWStartIncidence hexAWOrigin
  rw [hexAW_mem_vertexSet_iff]
  simp [hexAWNeighbor, hexAWOriginCoord, hexAWInStrip,
    hexAWBookRe2, hexAWBookSqrt3Im2, hexAWDepth, hexAWLong,
    hexAWTrans]


@[simp] theorem hexAWStartIncidence_reflect (T L : ℕ) (hT : 0 < T) :
    hexAWReflectIncidence (hexAWStartIncidence T L hT) =
      hexAWStartIncidence T L hT := by
  rw [hexAWReflectIncidence, hexAWStartIncidence, HexIncidence.mk.injEq]
  constructor
  · apply Subtype.ext
    rfl
  · rfl


theorem hexAWReflectIncidence_fixed_shape {T L : ℕ}
    (e : HexAWIncidence T L) (he : hexAWReflectIncidence e = e) :
    e.vtx.1.i = e.vtx.1.j ∧ e.edge = 0 := by
  have hv : (hexAWReflectIncidence e).vtx.1 = e.vtx.1 :=
    congrArg (fun q => q.vtx.1) he
  have hedge : (hexAWReflectIncidence e).edge = e.edge :=
    congrArg HexIncidence.edge he
  change hexAWReflectCoord e.vtx.1 = e.vtx.1 at hv
  change hexAWReflectEdge e.edge = e.edge at hedge
  rcases hcoord : e.vtx.1 with ⟨i, j, color⟩
  rw [hcoord] at hv
  change (⟨j, i, color⟩ : HexAWCoord) = ⟨i, j, color⟩ at hv
  have hij : i = j := by
    exact congrArg HexAWCoord.i hv |>.symm
  have he0 : e.edge = 0 := by
    exact (hexAWReflectEdge_fixed_iff e.edge).mp hedge
  exact ⟨hij, he0⟩


end
end StatMech.Universality
