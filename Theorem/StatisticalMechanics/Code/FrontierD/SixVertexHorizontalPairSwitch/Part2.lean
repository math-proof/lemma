/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalPairSwitch.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalColumnClassification
import Def.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalPairSwitch.Part2
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem boolPairAgreementCount_eq_cross_of_left_eq
    {a b c d : Bool} (h : a = b) :
    boolPairAgreementCount a b c d =
      boolPairCrossAgreementCount a b c d := by
  subst b
  cases a <;> cases c <;> cases d <;> decide

theorem boolPairAgreementCount_eq_cross_of_right_eq
    {a b c d : Bool} (h : c = d) :
    boolPairAgreementCount a b c d =
      boolPairCrossAgreementCount a b c d := by
  subst d
  cases a <;> cases b <;> cases c <;> decide


theorem boolPairAgreementCount_add_cross_of_mixed
    {a b c d : Bool} (hab : a ≠ b) (hcd : c ≠ d) :
    boolPairAgreementCount a b c d +
      boolPairCrossAgreementCount a b c d = 2 := by
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp_all [boolPairAgreementCount, boolPairCrossAgreementCount]

end
end StatMech.FrontierD
