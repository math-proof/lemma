/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/ScratchSixVertexAlignedFirstReturn.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoDisagreementStrand.Part16
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialCheckerboard
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialBoundaryToggleParity.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FiniteFirstReturn.Part8
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairSwitchNoUnitCounterexample.Part2
import Def.StatisticalMechanics.Code.FrontierD.ScratchSixVertexAlignedFirstReturn.Part23
open StatMech.FrontierD


namespace ScratchLocalRetieC

theorem doubledAlignedCharge_zeroOrUnit
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (x : DoubledAlignedState omega eta) :
    doubledAlignedCharge hdegree x = 0 \/
      doubledAlignedCharge hdegree x = 1 \/
      doubledAlignedCharge hdegree x = -1 := by
  rcases x with ⟨d, branch⟩
  cases branch
  · by_cases hzero : sixVertexDegreeTwoStrandStepSeamSign hdegree d = 0
    · exact Or.inl (by simpa [doubledAlignedCharge] using hzero)
    · exact Or.inr (by
        simpa [doubledAlignedCharge] using
          sixVertexDegreeTwoStrandStepSeamSign_of_ne_zero hdegree d hzero)
  · exact Or.inl (by simp [doubledAlignedCharge])

theorem sum_doubledAlignedCharge
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (hdegree : SixVertexLocallyDegreeTwo omega eta) :
    (∑ d : SixVertexOrientedDisagreementDart omega eta,
      ∑ branch : Bool,
        doubledAlignedCharge hdegree (d, branch)) =
      ∑ d : SixVertexOrientedDisagreementDart omega eta,
        sixVertexDegreeTwoStrandStepSeamSign hdegree d := by
  classical
  apply Finset.sum_congr rfl
  intro d hd
  simp [doubledAlignedCharge]

theorem sum_doubledAlignedCharge_eq_two
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (n : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = n - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = n + 1)
    (hn : 0 < n) :
    (∑ d : SixVertexOrientedDisagreementDart omega eta,
      ∑ branch : Bool,
        doubledAlignedCharge hdegree (d, branch)) = 2 := by
  rw [sum_doubledAlignedCharge]
  exact sum_sixVertexDegreeTwoStrandStepSeamSign_eq_two
    homega heta hdegree n homegaSector hetaSector hn

end ScratchLocalRetieC
