import Mathlib
import sympy.Basic
import Def.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPhysicalCommonFactor.Part3
open StatMech StatMech.FrontierD


/--
[SixVertexConfigurationPhysicalFiberExtension.targetEquiv_liftBranch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexConfigurationPhysicalCommonFactor.lean)
-/
@[path]
private lemma targetEquiv_liftBranch_eq
  {smallT largeT : EvenTorus}
  {smallMiddle : Fin (smallT.width + 1)}
  {largeMiddle : Fin (largeT.width + 1)}
  {hsmall_pos : 0 < smallMiddle.val}
  {hsmall_lt : smallMiddle.val < smallT.width}
  {hlarge_pos : 0 < largeMiddle.val}
  {hlarge_lt : largeMiddle.val < largeT.width}
  {embeddings : SixVertexConfigurationPhysicalPairedBranchEmbeddings smallT smallMiddle hsmall_pos hsmall_lt}
  {extension : SixVertexConfigurationPhysicalFiberExtension smallT largeT smallMiddle largeMiddle hsmall_pos hsmall_lt hlarge_pos hlarge_lt embeddings}
  {choice : Bool}
  {source : SixVertexConfigurationPhysicalSource largeT largeMiddle hlarge_pos hlarge_lt} :
-- imply
  extension.targetEquiv (extension.liftBranch choice source) = ⟨embeddings.branch choice (extension.sourceEquiv source).1, extension.fiberBranch choice (extension.sourceEquiv source).1 (extension.sourceEquiv source).2⟩ := by
-- proof
  apply StatMech.FrontierD.SixVertexConfigurationPhysicalFiberExtension.targetEquiv_liftBranch extension choice source

/--
[SixVertexConfigurationPhysicalFiberExtension.liftBranch_totalC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexConfigurationPhysicalCommonFactor.lean)
-/
@[path]
private lemma liftBranch_totalC_eq
  {smallT largeT : EvenTorus}
  {smallMiddle : Fin (smallT.width + 1)}
  {largeMiddle : Fin (largeT.width + 1)}
  {hsmall_pos : 0 < smallMiddle.val}
  {hsmall_lt : smallMiddle.val < smallT.width}
  {hlarge_pos : 0 < largeMiddle.val}
  {hlarge_lt : largeMiddle.val < largeT.width}
  {embeddings : SixVertexConfigurationPhysicalPairedBranchEmbeddings smallT smallMiddle hsmall_pos hsmall_lt}
  {extension : SixVertexConfigurationPhysicalFiberExtension smallT largeT smallMiddle largeMiddle hsmall_pos hsmall_lt hlarge_pos hlarge_lt embeddings}
  {choice : Bool}
  {source : SixVertexConfigurationPhysicalSource largeT largeMiddle hlarge_pos hlarge_lt} :
-- imply
  sixVertexConfigurationPairTotalCPhysical (extension.liftBranch choice source) = sixVertexConfigurationPairTotalCPhysical (embeddings.branch choice (extension.sourceEquiv source).1) + extension.targetFiberTotalC (embeddings.branch choice (extension.sourceEquiv source).1) (extension.fiberBranch choice (extension.sourceEquiv source).1 (extension.sourceEquiv source).2) := by
-- proof
  apply StatMech.FrontierD.SixVertexConfigurationPhysicalFiberExtension.liftBranch_totalC extension choice source


-- created on 2026-10-23
