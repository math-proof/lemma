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
import Theorem.StatisticalMechanics.Code.Universality.HexContentHalfBound.Part2


namespace StatMech.Universality

open scoped BigOperators

noncomputable section

noncomputable def hchb_bridges
    (S : Finset HexHWContentHalf) : Finset HexBridge := by
  classical
  exact S.biUnion (fun s => s.1.toFinset)


noncomputable def hchb_active (S : Finset HexHWContentHalf) : Finset ℕ :=
  S.biUnion hhc_widths


noncomputable def hchb_choices (S : Finset HexHWContentHalf) (T : ℕ) :
    Finset (Option HexBridge) := by
  classical
  exact insert none
    (((hchb_bridges S).filter (fun b => b.width = T)).image some)


def hchb_choiceWeight (x : ℝ) (_T : ℕ) : Option HexBridge → ℝ
  | none => 1
  | some b => hhc_bridgeWeight x b


noncomputable def hchb_bridgeMass
    (S : Finset HexHWContentHalf) (x : ℝ) (T : ℕ) : ℝ := by
  classical
  exact ∑ b ∈ (hchb_bridges S).filter (fun b => b.width = T),
    hhc_bridgeWeight x b

end
end StatMech.Universality
