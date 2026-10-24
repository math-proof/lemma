import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.FKRectBoundaryMergePrimitiveContradiction
open SimpleGraph StatMech StatMech.FrontierD


/--
[fkRectBoundaryMerge_sameSign_dependent_contradiction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryMergePrimitiveContradiction.lean)
-/
@[path]
private lemma fkRectBoundaryMerge_sameSign_dependent_contradiction_eq
  {R : FKRectTorus}
  {F : Finset R.EdgeIndex}
  {e : R.EdgeIndex}
-- given
  (heF : e ∉ F)
  (hmerge : ¬ (fkMedialLoopGraph R.medialTorus (fkRectConfigurationToMedialPairing R (fkRectConfigurationOfEdges R F))).Reachable (fkMedialWestDart (fkRectMedialVertexOfEdge R e)) (fkMedialEastDart (fkRectMedialVertexOfEdge R e)))
  (hnonzero0 : fkRectBoundaryMergeOldWinding0 R F e ≠ 0)
  (hnonzero1 : fkRectBoundaryMergeOldWinding1 R F e ≠ 0)
  (hdependent : ¬ FKRectWindingIndependent (fkRectBoundaryMergeOldWinding0 R F e) (fkRectBoundaryMergeOldWinding1 R F e))
  (hsign : 0 < (fkRectBoundaryMergeOldWinding0 R F e).1 * (fkRectBoundaryMergeOldWinding1 R F e).1 ∨ 0 < (fkRectBoundaryMergeOldWinding0 R F e).2 * (fkRectBoundaryMergeOldWinding1 R F e).2) :
-- imply
  False := by
-- proof
  apply StatMech.FrontierD.fkRectBoundaryMerge_sameSign_dependent_contradiction R F e heF hmerge hnonzero0 hnonzero1 hdependent hsign

/--
[fkRectBoundarySplit_sameSign_dependent_contradiction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryMergePrimitiveContradiction.lean)
-/
@[path]
private lemma fkRectBoundarySplit_sameSign_dependent_contradiction_eq
  {R : FKRectTorus}
  {F : Finset R.EdgeIndex}
  {e : R.EdgeIndex}
-- given
  (heF : e ∉ F)
  (hsplit : (fkMedialLoopGraph R.medialTorus (fkRectConfigurationToMedialPairing R (fkRectConfigurationOfEdges R F))).Reachable (fkMedialWestDart (fkRectMedialVertexOfEdge R e)) (fkMedialEastDart (fkRectMedialVertexOfEdge R e)))
  (hnonzero0 : fkRectBoundaryMergeNewWinding R F e ≠ 0)
  (hnonzero1 : fkRectBoundarySplitNewWinding1 R F e ≠ 0)
  (hdependent : ¬ FKRectWindingIndependent (fkRectBoundaryMergeNewWinding R F e) (fkRectBoundarySplitNewWinding1 R F e))
  (hsign : 0 < (fkRectBoundaryMergeNewWinding R F e).1 * (fkRectBoundarySplitNewWinding1 R F e).1 ∨ 0 < (fkRectBoundaryMergeNewWinding R F e).2 * (fkRectBoundarySplitNewWinding1 R F e).2) :
-- imply
  False := by
-- proof
  apply StatMech.FrontierD.fkRectBoundarySplit_sameSign_dependent_contradiction R F e heF hsplit hnonzero0 hnonzero1 hdependent hsign

/--
[fkRectBoundarySplit_nonzero_winding_persists_exactly_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryMergePrimitiveContradiction.lean)
-/
@[path]
private lemma fkRectBoundarySplit_nonzero_winding_persists_exactly_one_eq
  {R : FKRectTorus}
  {F : Finset R.EdgeIndex}
  {e : R.EdgeIndex}
-- given
  (heF : e ∉ F)
  (hsplit : (fkMedialLoopGraph R.medialTorus (fkRectConfigurationToMedialPairing R (fkRectConfigurationOfEdges R F))).Reachable (fkMedialWestDart (fkRectMedialVertexOfEdge R e)) (fkMedialEastDart (fkRectMedialVertexOfEdge R e)))
  (holdNonzero : fkRectBoundaryMergeOldWinding0 R F e ≠ 0)
  (hdependent : ¬ FKRectWindingIndependent (fkRectBoundaryMergeNewWinding R F e) (fkRectBoundarySplitNewWinding1 R F e)) :
-- imply
  (fkRectBoundaryMergeNewWinding R F e = 0 ∧ fkRectBoundarySplitNewWinding1 R F e = fkRectBoundaryMergeOldWinding0 R F e) ∨ (fkRectBoundaryMergeNewWinding R F e = fkRectBoundaryMergeOldWinding0 R F e ∧ fkRectBoundarySplitNewWinding1 R F e = 0) := by
-- proof
  apply StatMech.FrontierD.fkRectBoundarySplit_nonzero_winding_persists_exactly_one R F e heF hsplit holdNonzero hdependent

/--
[fkRectBoundaryMerge_nonzero_winding_from_exactly_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryMergePrimitiveContradiction.lean)
-/
@[path]
private lemma fkRectBoundaryMerge_nonzero_winding_from_exactly_one_eq
  {R : FKRectTorus}
  {F : Finset R.EdgeIndex}
  {e : R.EdgeIndex}
-- given
  (heF : e ∉ F)
  (hmerge : ¬ (fkMedialLoopGraph R.medialTorus (fkRectConfigurationToMedialPairing R (fkRectConfigurationOfEdges R F))).Reachable (fkMedialWestDart (fkRectMedialVertexOfEdge R e)) (fkMedialEastDart (fkRectMedialVertexOfEdge R e)))
  (hnewNonzero : fkRectBoundaryMergeNewWinding R F e ≠ 0)
  (hdependent : ¬ FKRectWindingIndependent (fkRectBoundaryMergeOldWinding0 R F e) (fkRectBoundaryMergeOldWinding1 R F e)) :
-- imply
  (fkRectBoundaryMergeOldWinding0 R F e = 0 ∧ fkRectBoundaryMergeOldWinding1 R F e = fkRectBoundaryMergeNewWinding R F e) ∨ (fkRectBoundaryMergeOldWinding0 R F e = fkRectBoundaryMergeNewWinding R F e ∧ fkRectBoundaryMergeOldWinding1 R F e = 0) := by
-- proof
  apply StatMech.FrontierD.fkRectBoundaryMerge_nonzero_winding_from_exactly_one R F e heF hmerge hnewNonzero hdependent


-- created on 2026-10-23
