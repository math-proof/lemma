/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexConfigurationPhysicalCommonFactor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPhysicalPairedBranch.Part2
import Structure.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPhysicalCommonFactor.Part2


namespace StatMech.FrontierD

noncomputable section

def SixVertexConfigurationPhysicalFiberExtension.liftBranch
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
    (choice : Bool) :
    SixVertexConfigurationPhysicalSource largeT largeMiddle
        hlarge_pos hlarge_lt ↪
      SixVertexConfigurationPhysicalTarget largeT largeMiddle :=
  extension.sourceEquiv.toEmbedding |>.trans
    (Function.Embedding.sigmaMap (embeddings.branch choice)
      (extension.fiberBranch choice)) |>.trans
    extension.targetEquiv.symm.toEmbedding

end
end StatMech.FrontierD
