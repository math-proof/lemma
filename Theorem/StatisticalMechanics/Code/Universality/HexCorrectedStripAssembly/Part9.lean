/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripGeometry.Part11
import Def.StatisticalMechanics.Code.Universality.HexCorrectedStripAssembly.Part10


namespace StatMech.Universality

open Complex HexWalk Set

open scoped BigOperators

noncomputable section

theorem hexCSHeading_geometry {T L : ℕ} (v : HexCSVertex T L)
    (e : Fin 3) :
    hexAWMid v.1 e - hexAWPos v.1 =
      (1 / 2 : ℂ) * hexUnit (hexCSHeading v e) := by
  rw [hexCSHeading, hexCSCanonicalHeading_unit]
  exact hexAWMid_sub_pos v.1 e

theorem hexCSPairIndex_ne_start {T L : ℕ} {hT : 0 < T}
    (i : HexCSPairIndex T L) :
    i.1 ≠ hexCSStartIncidence T L hT := by
  intro hs
  apply hexCSPairIndex_ne_reflect i
  calc
    i.1 = hexCSStartIncidence T L hT := hs
    _ = hexCSReflectIncidence (hexCSStartIncidence T L hT) :=
      (hexCSStartIncidence_reflect T L hT).symm
    _ = hexCSReflectIncidence i.1 :=
      congrArg hexCSReflectIncidence hs.symm

theorem hexCSReflectIncidence_mid {T L : ℕ}
    (e : HexCSIncidence T L) :
    hexAWMid (hexCSReflectIncidence e).vtx.1
        (hexCSReflectIncidence e).edge =
      hsc_refl hexAWStart 1 (hexAWMid e.vtx.1 e.edge) := by
  exact (hexAWMid_reflect_one e.vtx.1 e.edge).symm


end
end StatMech.Universality
