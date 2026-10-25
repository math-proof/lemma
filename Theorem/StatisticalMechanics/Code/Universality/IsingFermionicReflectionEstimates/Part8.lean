/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicReflectionEstimates.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicLineGambler.Part3
import Def.StatisticalMechanics.Code.Universality.IsingFermionicReflectionEstimates.Part8


namespace StatMech.Universality

namespace IsingDiagonalWalkHitSplit

theorem survivalExceptionalPointwiseProjection_injective
    (R level walkLength : Nat) (start target : Int × Int)
    (hstart : start.1 + 1 = level) (hlevel : 0 < level)
    (hgap : level + 1 < R) :
    Function.Injective
      (survivalExceptionalPointwiseProjection R level walkLength start target
        hstart hlevel hgap) := by
  intro a b hab
  apply survivalExceptionalFirstHitFamily_projection_injective R level
    walkLength start target hstart hlevel hgap
  apply Prod.ext
  · simpa [survivalExceptionalPointwiseProjection,
        survivalExceptionalProjection] using
      congrArg (fun z => z.1) hab
  · apply Subtype.ext
    simpa [survivalExceptionalPointwiseProjection,
        survivalExceptionalProjection] using
      congrArg (fun z => z.2.1) hab

theorem
    natCard_survivalExceptionalFirstHitFamily_le_line_mul_vertical
    (R level walkLength : Nat) (start target : Int × Int)
    (hstart : start.1 + 1 = level) (hlevel : 0 < level)
    (hgap : level + 1 < R) :
    Nat.card (SurvivalExceptionalFirstHitFamily R start (level : Int)
        walkLength target) ≤
      Nat.card (IsingLineChoicePathFamily (R - level) walkLength
        (rightGapNeighbor R level hgap) (rightGapLeft R level)) *
      Nat.card (VerticalChoicePathFamily walkLength start.2 target.2) := by
  calc
    Nat.card (SurvivalExceptionalFirstHitFamily R start (level : Int)
        walkLength target) ≤
        Nat.card (IsingLineChoicePathFamily (R - level) walkLength
            (rightGapNeighbor R level hgap) (rightGapLeft R level) ×
          VerticalChoicePathFamily walkLength start.2 target.2) :=
      Nat.card_le_card_of_injective
        (survivalExceptionalPointwiseProjection R level walkLength start target
          hstart hlevel hgap)
        (survivalExceptionalPointwiseProjection_injective R level walkLength
          start target hstart hlevel hgap)
    _ = _ := by rw [Nat.card_prod]

end IsingDiagonalWalkHitSplit
end StatMech.Universality
