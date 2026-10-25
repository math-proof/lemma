/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexConfigurationPhysicalCommonFactor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPhysicalPairedBranch.Part2
import Def.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPhysicalCommonFactor


namespace StatMech.FrontierD

noncomputable section

structure SixVertexConfigurationPhysicalFiberExtension
    (smallT largeT : EvenTorus)
    (smallMiddle : Fin (smallT.width + 1))
    (largeMiddle : Fin (largeT.width + 1))
    (hsmall_pos : 0 < smallMiddle.val)
    (hsmall_lt : smallMiddle.val < smallT.width)
    (hlarge_pos : 0 < largeMiddle.val)
    (hlarge_lt : largeMiddle.val < largeT.width)
    (embeddings : SixVertexConfigurationPhysicalPairedBranchEmbeddings
      smallT smallMiddle hsmall_pos hsmall_lt) where
  SourceFiber :
    SixVertexConfigurationPhysicalSource smallT smallMiddle
      hsmall_pos hsmall_lt → Type
  TargetFiber :
    SixVertexConfigurationPhysicalTarget smallT smallMiddle → Type
  sourceEquiv :
    SixVertexConfigurationPhysicalSource largeT largeMiddle
        hlarge_pos hlarge_lt ≃
      Sigma SourceFiber
  targetEquiv :
    SixVertexConfigurationPhysicalTarget largeT largeMiddle ≃
      Sigma TargetFiber
  sourceFiberTotalC : forall base, SourceFiber base → Nat
  targetFiberTotalC : forall base, TargetFiber base → Nat
  source_totalC : forall source,
    sixVertexConfigurationPairTotalCPhysical source =
      sixVertexConfigurationPairTotalCPhysical (sourceEquiv source).1 +
        sourceFiberTotalC (sourceEquiv source).1 (sourceEquiv source).2
  target_totalC : forall target,
    sixVertexConfigurationPairTotalCPhysical target =
      sixVertexConfigurationPairTotalCPhysical (targetEquiv target).1 +
        targetFiberTotalC (targetEquiv target).1 (targetEquiv target).2
  fiberBranch : forall choice base,
    SourceFiber base ↪ TargetFiber (embeddings.branch choice base)
  fiberAggregateTotalC : forall base fiber,
    2 * sourceFiberTotalC base fiber <=
      targetFiberTotalC (embeddings.branch false base)
          (fiberBranch false base fiber) +
        targetFiberTotalC (embeddings.branch true base)
          (fiberBranch true base fiber)


end
end StatMech.FrontierD
