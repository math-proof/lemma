/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthStripGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexFiniteStripEnum.Part6
import Theorem.StatisticalMechanics.Code.Universality.HexStripCountsClose.Part3
import Def.StatisticalMechanics.Code.Universality.HexAllWidthStripGeometry.Part10


namespace StatMech.Universality

open Complex HexWalk

noncomputable section

@[simp] theorem hexAWReflectIncidence_invol {T L : ℕ}
    (e : HexAWIncidence T L) :
    hexAWReflectIncidence (hexAWReflectIncidence e) = e := by
  cases e with
  | mk v edge =>
    rw [hexAWReflectIncidence, hexAWReflectIncidence,
      HexIncidence.mk.injEq]
    exact ⟨hexAWReflectVertex_invol v, hexAWReflectEdge_invol edge⟩

theorem hexAWReflectIncidence_mid {T L : ℕ}
    (e : HexAWIncidence T L) :
    hexAWMid (hexAWReflectIncidence e).vtx.1
        (hexAWReflectIncidence e).edge =
      hsc_refl hexAWStart 4 (hexAWMid e.vtx.1 e.edge) := by
  exact (hexAWMid_reflect e.vtx.1 e.edge).symm


end
end StatMech.Universality
