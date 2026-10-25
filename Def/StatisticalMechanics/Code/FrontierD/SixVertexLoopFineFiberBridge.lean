/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexLoopFineFiberBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexLoopDecoratedUnitTransfer
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairTwoCycleCompletionHall.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalFineFiberFactorization.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalEdgeDegreeHall.Part6
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexLoopFineFiberBridge


namespace StatMech.FrontierD

noncomputable section

noncomputable def sixVertexLoopFineProfileFiberEquiv
    (T : EvenTorus) (left right : Fin (T.width + 1))
    (profile : SixVertexHorizontalBoundedFineRowProfile T) :
    SixVertexLoopDecoratedPairFineProfileFiber T left right profile ≃
      (SixVertexConfigurationPairFineProfileFiber T left right profile ×
        Fin (2 ^ (sixVertexHorizontalFineRowProfileGrade profile).1)) where
  toFun decorated :=
    let hprofile : sixVertexHorizontalPairBoundedFineRowProfile
        (decorated.1.1.1.1.horizontal,
          decorated.1.1.2.1.horizontal) = profile := by
      simpa using decorated.2
    let pair : SixVertexConfigurationPairFineProfileFiber
        T left right profile := ⟨decorated.1.1, hprofile⟩
    let htotal := sixVertexConfigurationPairTotalC_eq_fineProfileGrade pair
    (pair, sixVertexCompatibleLoopPairingPairEquivFin
      pair.1 (sixVertexHorizontalFineRowProfileGrade profile).1 htotal
      decorated.1.2)
  invFun decorated :=
    let htotal := sixVertexConfigurationPairTotalC_eq_fineProfileGrade
      decorated.1
    ⟨⟨decorated.1.1,
        (sixVertexCompatibleLoopPairingPairEquivFin decorated.1.1
          (sixVertexHorizontalFineRowProfileGrade profile).1 htotal).symm
          decorated.2⟩,
      by simpa using decorated.1.2⟩
  left_inv decorated := by
    apply Subtype.ext
    apply Sigma.ext
    · rfl
    · simp
  right_inv decorated := by
    apply Prod.ext
    · rfl
    · simp

end
end StatMech.FrontierD
