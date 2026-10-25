/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexClassification.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexLattice.Part11
import Theorem.StatisticalMechanics.Code.Universality.HexVertex.Part5
import Def.StatisticalMechanics.Code.Universality.HexVertexEnum.Part5
import Theorem.StatisticalMechanics.Code.Universality.HexVertexBijection.Part5
import Theorem.StatisticalMechanics.Code.Universality.HexVertexSeparation.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexVertexCoverage


namespace StatMech.Universality

open Complex

open Function

open HexWalk

variable {region : ℂ → Prop} {a : ℂ} {h0 : ℤ} {v du : ℂ}


theorem hexClass_endsAt_passesThrough (ts : List ℤ) (z : ℂ)
    (h : (ofTurns a h0 ts).EndsAt z) : PassesThrough a h0 ts z := by
  unfold PassesThrough
  unfold HexWalk.EndsAt at h
  have hne : (ofTurns a h0 ts).mids ≠ [] := by
    intro hnil
    have := HexWalk.length_mids (ofTurns a h0 ts)
    rw [hnil] at this
    simp at this
  rw [← h]
  exact List.getLast_mem hne


theorem hexClass_specialMidCount_three_of_passes (ts : List ℤ)
    (hp : PassesThrough a h0 ts (v + du))
    (hq : PassesThrough a h0 ts (v + hexOmega * du))
    (hr : PassesThrough a h0 ts (v + hexOmega ^ 2 * du)) :
    specialMidCount a h0 v du ts = 3 := by
  classical
  unfold specialMidCount
  rw [if_pos hp, if_pos hq, if_pos hr]


end StatMech.Universality
