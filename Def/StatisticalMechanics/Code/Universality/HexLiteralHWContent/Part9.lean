/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWContent.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.Universality.HexBridgeDecomp.Part9
import Theorem.StatisticalMechanics.Code.Universality.HexBridgeWeight.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralCountLaws.Part3
import Def.StatisticalMechanics.Code.Universality.HexW2Cut.Part5
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWContent.Part8


namespace StatMech.Universality

open HexWalk

open scoped BigOperators


noncomputable def hhc_halfOfList (ts : List ℤ) : HexHWContentHalf := by
  classical
  by_cases hne : ts = []
  · exact ⟨[], strictDecreasingWidths_nil⟩
  · exact ⟨[hhc_bridgeOfNonempty ts hne], by
      simp [StrictDecreasingWidths]⟩


end StatMech.Universality
