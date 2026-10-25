/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexConfigurationPhysicalCommonFactor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPhysicalPairedBranch.Part2
import Def.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPhysicalCommonFactor.Part2


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem
    SixVertexConfigurationPhysicalFiberExtension.targetEquiv_liftBranch
    {smallT largeT : EvenTorus}
    {smallMiddle : Fin (smallT.width + 1)}
    {largeMiddle : Fin (largeT.width + 1)}
    {hsmall_pos : 0 < smallMiddle.val}
    {hsmall_lt : smallMiddle.val < smallT.width}
    {hlarge_pos : 0 < largeMiddle.val}
    {hlarge_lt : largeMiddle.val < largeT.width}
    {embeddings : SixVertexConfigurationPhysicalPairedBranchEmbeddings
      smallT smallMiddle hsmall_pos hsmall_lt}
    (extension : SixVertexConfigurationPhysicalFiberExtension
      smallT largeT smallMiddle largeMiddle hsmall_pos hsmall_lt
      hlarge_pos hlarge_lt embeddings)
    (choice : Bool)
    (source : SixVertexConfigurationPhysicalSource largeT largeMiddle
      hlarge_pos hlarge_lt) :
    extension.targetEquiv (extension.liftBranch choice source) =
      ⟨embeddings.branch choice (extension.sourceEquiv source).1,
        extension.fiberBranch choice (extension.sourceEquiv source).1
          (extension.sourceEquiv source).2⟩ := by
  change extension.targetEquiv (extension.targetEquiv.symm _) = _
  rw [Equiv.apply_symm_apply]
  rfl

theorem SixVertexConfigurationPhysicalFiberExtension.liftBranch_totalC
    {smallT largeT : EvenTorus}
    {smallMiddle : Fin (smallT.width + 1)}
    {largeMiddle : Fin (largeT.width + 1)}
    {hsmall_pos : 0 < smallMiddle.val}
    {hsmall_lt : smallMiddle.val < smallT.width}
    {hlarge_pos : 0 < largeMiddle.val}
    {hlarge_lt : largeMiddle.val < largeT.width}
    {embeddings : SixVertexConfigurationPhysicalPairedBranchEmbeddings
      smallT smallMiddle hsmall_pos hsmall_lt}
    (extension : SixVertexConfigurationPhysicalFiberExtension
      smallT largeT smallMiddle largeMiddle hsmall_pos hsmall_lt
      hlarge_pos hlarge_lt embeddings)
    (choice : Bool)
    (source : SixVertexConfigurationPhysicalSource largeT largeMiddle
      hlarge_pos hlarge_lt) :
    sixVertexConfigurationPairTotalCPhysical
        (extension.liftBranch choice source) =
      sixVertexConfigurationPairTotalCPhysical
          (embeddings.branch choice (extension.sourceEquiv source).1) +
        extension.targetFiberTotalC
          (embeddings.branch choice (extension.sourceEquiv source).1)
          (extension.fiberBranch choice
            (extension.sourceEquiv source).1
            (extension.sourceEquiv source).2) := by
  rw [extension.target_totalC]
  rw [extension.targetEquiv_liftBranch]


end
end StatMech.FrontierD
