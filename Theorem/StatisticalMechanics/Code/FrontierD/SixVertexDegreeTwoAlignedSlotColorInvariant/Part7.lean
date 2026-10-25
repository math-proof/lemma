/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoAlignedSlotColorInvariant.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexTransitionRetieExact.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexRoutedKeySlotColorInvariant.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoCanonicalUnitRoute.Part2
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoAlignedSlotColorInvariant.Part7


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexDegreeTwoAlignedTrueFirstReturn_arrival
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (x : DoubledAlignedState omega eta) :
    finiteFirstReturn
        (alignedBoundaryPerm homega heta hdegree true)
        (activeBlackDart (omega := omega) (eta := eta))
        (doubledAlignedBlackDartEquiv homega heta hdegree true x) =
      doubledAlignedBlackDartEquiv homega heta hdegree true
        (sixVertexDegreeTwoAlignedTrueFirstReturnState
          homega heta hdegree x) := by
  let y := doubledAlignedFirstReturnPerm homega heta hdegree x
  let retie := orientedDartAlignedRetie homega heta hdegree y.1
  have hcommon := doubledAlignedFirstReturnPerm_true_common_arrival
    homega heta hdegree x
  apply Subtype.ext
  unfold sixVertexDegreeTwoAlignedTrueFirstReturnState
  change (finiteFirstReturn
      (alignedBoundaryPerm homega heta hdegree true)
      (activeBlackDart (omega := omega) (eta := eta))
      (doubledAlignedBlackDartEquiv homega heta hdegree true x)).1 =
    (doubledAlignedBlackDartEquiv homega heta hdegree true
      (if retie.pairingP = retie.pairingQ then y
        else doubledAlignedBranchSwap y)).1
  by_cases heq : retie.pairingP = retie.pairingQ
  · rw [if_pos heq]
    have hdart := doubledAlignedBlackDart_true_eq_false_or_branchSwap
      homega heta hdegree y
    dsimp only at hdart
    rw [if_pos heq] at hdart
    exact hcommon.trans hdart.symm
  · rw [if_neg heq]
    have hdart := doubledAlignedBlackDart_true_eq_false_or_branchSwap
      homega heta hdegree (doubledAlignedBranchSwap y)
    simp only [doubledAlignedBranchSwap_fst,
      doubledAlignedBranchSwap_self] at hdart
    rw [if_neg heq] at hdart
    exact hcommon.trans hdart.symm

theorem sixVertexDegreeTwoBranchClosedSelected_trueFirstReturn
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (x : DoubledAlignedState omega eta) :
    sixVertexDegreeTwoBranchClosedSelected homega heta hdegree middle
        homegaSector hetaSector hmiddle
        (sixVertexDegreeTwoAlignedTrueFirstReturnState
          homega heta hdegree x) =
      sixVertexDegreeTwoBranchClosedSelected homega heta hdegree middle
        homegaSector hetaSector hmiddle
        (doubledAlignedFirstReturnPerm homega heta hdegree x) := by
  let y := doubledAlignedFirstReturnPerm homega heta hdegree x
  let retie := orientedDartAlignedRetie homega heta hdegree y.1
  change sixVertexDegreeTwoBranchClosedSelected homega heta hdegree middle
      homegaSector hetaSector hmiddle
      (if retie.pairingP = retie.pairingQ then y
        else doubledAlignedBranchSwap y) =
    sixVertexDegreeTwoBranchClosedSelected homega heta hdegree middle
      homegaSector hetaSector hmiddle y
  split
  · rfl
  · exact sixVertexDegreeTwoBranchClosedSelected_branchSwap
      homega heta hdegree middle homegaSector hetaSector hmiddle _


end
end StatMech.FrontierD
