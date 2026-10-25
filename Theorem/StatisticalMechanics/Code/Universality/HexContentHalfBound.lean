/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexContentHalfBound.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexContentChoiceBound
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWContent.Part12
import Theorem.StatisticalMechanics.Code.Universality.HexSurgerySeams.Part5
import Instance.StatisticalMechanics.Code.Universality.HexContentHalfBound


namespace StatMech.Universality

open scoped BigOperators

noncomputable section

theorem hchb_eq_of_mem_iff (s t : HexHWContentHalf)
    (hmem : forall b : HexBridge, b ∈ s.1 ↔ b ∈ t.1) : s = t := by
  apply Subtype.ext
  exact s.2.eq_of_mem_iff t.2 hmem


end
end StatMech.Universality
