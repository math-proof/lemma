/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripColumn.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedColumnLength
import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripFamilyMass.Part2
import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripIdentity.Part2
import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripColumn


namespace StatMech.Universality

open HexWalk

open scoped BigOperators

noncomputable section

noncomputable def hexCSTopColumn
    (T : ℕ) (hT : 0 < T)
    (hlocal : ∀ L, HexCSLocalRelation T L hT)
    (hwindow : ∀ L, HexCSBoundaryWindowLaw T L hT) :
    HexColumn T hexChiE where
  W := {ts : List ℤ // HexCSTopWalkAtWidth T hT ts}
  len := fun w => (ofTurns hexAWStart 1 w.1).endpointNumVertices
  len_ge := fun w => hexCSTopWalkAtWidth_length_ge T hT w.1 w.2
  crit_summable := by
    apply summable_of_sum_le
    · intro w
      exact pow_nonneg (le_of_lt hexChiE_pos) _
    · exact hexCSTopAtWidth_finset_bound T hT hlocal hwindow
  crit_le_one := by
    apply Real.tsum_le_of_sum_le
    · intro w
      exact pow_nonneg (le_of_lt hexChiE_pos) _
    · exact hexCSTopAtWidth_finset_bound T hT hlocal hwindow

end
end StatMech.Universality
