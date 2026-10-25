/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralCountLaws.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexZConvClose.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexSurgerySeams.Part5
import Theorem.StatisticalMechanics.Code.Universality.HexHalfEdgeClose.Part3
import Def.StatisticalMechanics.Code.Universality.HexLiteralCountLaws


namespace StatMech.Universality

open HexWalk


theorem hlc_sawCount_zero (a : ℂ) (h0 : ℤ) : hlc_sawCount a h0 0 = 1 := by
  classical
  unfold hlc_sawCount hzc_sawCount
  have hfiber :
      (hzc_truncFinset a h0 (0 + 1 + 1)).filter
          (fun ts => (ofTurns a h0 ts).numVertices = 0 + 1) = {[]} := by
    ext ts
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨_, hlen⟩
      have hzero : ts.length = 0 := by
        simpa [numVertices] using hlen
      exact List.length_eq_zero_iff.mp hzero
    · rintro rfl
      refine ⟨hzc_nil_mem_truncFinset a h0 (by omega), ?_⟩
      rfl
  rw [hfiber, Finset.card_singleton]

@[simp]
theorem hlc_sawCountR_zero (a : ℂ) (h0 : ℤ) : hlc_sawCountR a h0 0 = 1 := by
  simp [hlc_sawCountR, hlc_sawCount_zero]


end StatMech.Universality
