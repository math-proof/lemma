/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexConfigurationPhysicalCommonFactor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPhysicalPairedBranch.Part2
import Structure.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPhysicalCommonFactor


namespace StatMech.FrontierD

noncomputable section

def SixVertexConfigurationPhysicalCommonFactor.liftBranch
    {smallT largeT : EvenTorus}
    {smallMiddle : Fin (smallT.width + 1)}
    {largeMiddle : Fin (largeT.width + 1)}
    {hsmall_pos : 0 < smallMiddle.val}
    {hsmall_lt : smallMiddle.val < smallT.width}
    {hlarge_pos : 0 < largeMiddle.val}
    {hlarge_lt : largeMiddle.val < largeT.width}
    (factorization : SixVertexConfigurationPhysicalCommonFactor
      smallT largeT smallMiddle largeMiddle hsmall_pos hsmall_lt
      hlarge_pos hlarge_lt)
    (embeddings : SixVertexConfigurationPhysicalPairedBranchEmbeddings
      smallT smallMiddle hsmall_pos hsmall_lt)
    (choice : Bool) :
    SixVertexConfigurationPhysicalSource largeT largeMiddle
        hlarge_pos hlarge_lt ↪
      SixVertexConfigurationPhysicalTarget largeT largeMiddle where
  toFun source :=
    factorization.targetEquiv.symm
      (embeddings.branch choice (factorization.sourceEquiv source).1,
        (factorization.sourceEquiv source).2)
  inj' := by
    intro first second heq
    have hpair := congrArg factorization.targetEquiv heq
    simp only [Equiv.apply_symm_apply] at hpair
    have hfirst := (embeddings.branch choice).injective
      (congrArg (fun pair => pair.1) hpair)
    have hsecond := congrArg (fun pair => pair.2) hpair
    exact factorization.sourceEquiv.injective (Prod.ext hfirst hsecond)


def SixVertexConfigurationPhysicalCommonFactor.lift
    {smallT largeT : EvenTorus}
    {smallMiddle : Fin (smallT.width + 1)}
    {largeMiddle : Fin (largeT.width + 1)}
    {hsmall_pos : 0 < smallMiddle.val}
    {hsmall_lt : smallMiddle.val < smallT.width}
    {hlarge_pos : 0 < largeMiddle.val}
    {hlarge_lt : largeMiddle.val < largeT.width}
    (factorization : SixVertexConfigurationPhysicalCommonFactor
      smallT largeT smallMiddle largeMiddle hsmall_pos hsmall_lt
      hlarge_pos hlarge_lt)
    (embeddings : SixVertexConfigurationPhysicalPairedBranchEmbeddings
      smallT smallMiddle hsmall_pos hsmall_lt) :
    SixVertexConfigurationPhysicalPairedBranchEmbeddings
      largeT largeMiddle hlarge_pos hlarge_lt where
  branch choice := factorization.liftBranch embeddings choice
  distinct source := by
    intro heq
    apply embeddings.distinct (factorization.sourceEquiv source).1
    have hpair := congrArg factorization.targetEquiv heq
    simpa [SixVertexConfigurationPhysicalCommonFactor.liftBranch] using
      congrArg Prod.fst hpair
  aggregateTotalC source := by
    have hsmall := embeddings.aggregateTotalC
      (factorization.sourceEquiv source).1
    rw [factorization.source_totalC,
      factorization.target_totalC, factorization.target_totalC]
    simp [SixVertexConfigurationPhysicalCommonFactor.liftBranch]
    omega


end
end StatMech.FrontierD
