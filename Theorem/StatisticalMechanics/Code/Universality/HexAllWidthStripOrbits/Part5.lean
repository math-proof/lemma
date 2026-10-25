/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthStripOrbits.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexAllWidthStripGeometry.Part18
import Theorem.StatisticalMechanics.Code.Universality.HexMirrorOrbitBoundary.Part3
import Def.StatisticalMechanics.Code.Universality.HexAllWidthStripOrbits.Part6


namespace StatMech.Universality

open Complex HexWalk Set

open scoped BigOperators

noncomputable section

theorem hexAWFixedIndex_eq_right {T L : ℕ} {hT : 0 < T}
    (k : HexAWFixedIndex T L hT) :
    ∃ n : ℕ, 0 < n ∧ T = 2 * n ∧
      k.1.vtx.1 = hexAWRightFixedCoord n ∧ k.1.edge = 0 := by
  obtain hstart | ⟨n, hTn, hcoord, hedge⟩ :=
    hexAW_fixed_boundary_classification k.1 k.2.1 k.2.2.1
  · exfalso
    apply k.2.2.2
    rw [HexIncidence.mk.injEq]
    exact ⟨Subtype.ext hstart.1, hstart.2⟩
  · have hn : 0 < n := by omega
    exact ⟨n, hn, hTn, hcoord, hedge⟩


theorem hexAWFixedIndex_isEmpty_of_odd {T L : ℕ} {hT : 0 < T}
    (hodd : Odd T) : IsEmpty (HexAWFixedIndex T L hT) := by
  constructor
  intro k
  obtain ⟨n, _, hTn, _⟩ := hexAWFixedIndex_eq_right k
  obtain ⟨m, hm⟩ := hodd
  omega


end
end StatMech.Universality
