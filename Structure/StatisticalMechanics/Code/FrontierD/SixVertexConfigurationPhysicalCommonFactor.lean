/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexConfigurationPhysicalCommonFactor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPhysicalPairedBranch.Part2


namespace StatMech.FrontierD

noncomputable section

structure SixVertexConfigurationPhysicalCommonFactor
    (smallT largeT : EvenTorus)
    (smallMiddle : Fin (smallT.width + 1))
    (largeMiddle : Fin (largeT.width + 1))
    (hsmall_pos : 0 < smallMiddle.val)
    (hsmall_lt : smallMiddle.val < smallT.width)
    (hlarge_pos : 0 < largeMiddle.val)
    (hlarge_lt : largeMiddle.val < largeT.width) where
  Factor : Type
  sourceEquiv :
    SixVertexConfigurationPhysicalSource largeT largeMiddle
        hlarge_pos hlarge_lt ≃
      SixVertexConfigurationPhysicalSource smallT smallMiddle
          hsmall_pos hsmall_lt × Factor
  targetEquiv :
    SixVertexConfigurationPhysicalTarget largeT largeMiddle ≃
      SixVertexConfigurationPhysicalTarget smallT smallMiddle × Factor
  factorTotalC : Factor → Nat
  source_totalC : forall source,
    sixVertexConfigurationPairTotalCPhysical source =
      sixVertexConfigurationPairTotalCPhysical (sourceEquiv source).1 +
        factorTotalC (sourceEquiv source).2
  target_totalC : forall target,
    sixVertexConfigurationPairTotalCPhysical target =
      sixVertexConfigurationPairTotalCPhysical (targetEquiv target).1 +
        factorTotalC (targetEquiv target).2


end
end StatMech.FrontierD
