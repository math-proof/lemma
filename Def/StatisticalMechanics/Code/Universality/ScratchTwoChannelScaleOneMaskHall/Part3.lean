/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelScaleOneMaskHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelDynamicEdgeEncoding.Part3
import Abbrev.StatisticalMechanics.Code.Universality.ScratchTwoChannelScaleOneMaskHall.Part3


namespace StatMech.Universality

def rlcScaleOneSectionAFactorEquiv :
    Equiv RlcScaleOneSectionAFailure RlcScaleOneSectionAFactors where
  toFun w :=
    (⟨![w.1 6, w.1 7], by
      simpa [rlcScaleOneSectionAAvoidsSelectedRoutes] using
        (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp w.2).1).1⟩,
    ⟨![w.1 0, w.1 1, w.1 2, w.1 3, w.1 4], by
      simpa [rlcScaleOneSectionAAvoidsSelectedRoutes] using
        (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp w.2).1).2⟩,
    ⟨![w.1 10, w.1 11, w.1 13, w.1 14, w.1 9], by
      simpa [rlcScaleOneSectionAAvoidsSelectedRoutes] using
        (Bool.and_eq_true_iff.mp w.2).2⟩,
    ![w.1 5, w.1 8, w.1 12])
  invFun blocks :=
    ⟨![blocks.2.1.1 0, blocks.2.1.1 1, blocks.2.1.1 2,
        blocks.2.1.1 3, blocks.2.1.1 4, blocks.2.2.2 0,
        blocks.1.1 0, blocks.1.1 1, blocks.2.2.2 1,
        blocks.2.2.1.1 4, blocks.2.2.1.1 0, blocks.2.2.1.1 1,
        blocks.2.2.2 2, blocks.2.2.1.1 2, blocks.2.2.1.1 3], by
      change (rlcScaleOnePairBlockAvoidsRoute blocks.1.1 &&
        rlcScaleOneFiveBlockAvoidsRoutes blocks.2.1.1 &&
        rlcScaleOneFiveBlockAvoidsRoutes blocks.2.2.1.1) = true
      rw [blocks.1.2, blocks.2.1.2, blocks.2.2.1.2]
      decide⟩
  left_inv w := by
    apply Subtype.ext
    funext i
    fin_cases i <;> rfl
  right_inv blocks := by
    rcases blocks with ⟨pair, left, right, unused⟩
    apply Prod.ext
    · apply Subtype.ext
      funext i
      fin_cases i <;> rfl
    · apply Prod.ext
      · apply Subtype.ext
        funext i
        fin_cases i <;> rfl
      · apply Prod.ext
        · apply Subtype.ext
          funext i
          fin_cases i <;> rfl
        · funext i
          fin_cases i <;> rfl

end StatMech.Universality
