import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectMedialPrimalLabel.Part3
open StatMech StatMech.FrontierD


/--
[fkRectMedialVertexOfEdge_fst_val](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectMedialPrimalLabel.lean)
-/
@[path]
private lemma fkRectMedialVertexOfEdge_fst_val_eq
  {R : FKRectTorus}
  {e : R.EdgeIndex} :
-- imply
  (fkRectMedialVertexOfEdge R e).1.val = e.1.toNat + 2 * e.2.1.val := by
-- proof
  apply StatMech.FrontierD.fkRectMedialVertexOfEdge_fst_val R e

/--
[fkRectMedialVertexOfEdge_snd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectMedialPrimalLabel.lean)
-/
@[path]
private lemma fkRectMedialVertexOfEdge_snd_eq
  {R : FKRectTorus}
  {e : R.EdgeIndex} :
-- imply
  (fkRectMedialVertexOfEdge R e).2 = e.2.2 := by
-- proof
  apply StatMech.FrontierD.fkRectMedialVertexOfEdge_snd R e

/--
[fkRectTorusMedialEdgeEquiv_symm_fst_val](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectMedialPrimalLabel.lean)
-/
@[path]
private lemma fkRectTorusMedialEdgeEquiv_symm_fst_val_eq
  {R : FKRectTorus}
  {e : R.EdgeIndex} :
-- imply
  ((fkRectTorusMedialEdgeEquiv R).symm e).1.val = e.1.toNat + 2 * e.2.1.val := by
-- proof
  apply StatMech.FrontierD.fkRectTorusMedialEdgeEquiv_symm_fst_val R e

/--
[fkRectTorusMedialEdgeEquiv_symm_snd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectMedialPrimalLabel.lean)
-/
@[path]
private lemma fkRectTorusMedialEdgeEquiv_symm_snd_eq
  {R : FKRectTorus}
  {e : R.EdgeIndex} :
-- imply
  ((fkRectTorusMedialEdgeEquiv R).symm e).2 = e.2.2 := by
-- proof
  apply StatMech.FrontierD.fkRectTorusMedialEdgeEquiv_symm_snd R e

/--
[fkRectTorusIndexedEdge_eq_medialPrimals](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectMedialPrimalLabel.lean)
-/
@[path]
private lemma fkRectTorusIndexedEdge_eq_medialPrimals_eq
  {R : FKRectTorus}
  {e : R.EdgeIndex} :
-- imply
  fkRectTorusIndexedEdge R e = s(fkRectMedialWestPrimal R e, fkRectMedialEastPrimal R e) := by
-- proof
  apply StatMech.FrontierD.fkRectTorusIndexedEdge_eq_medialPrimals R e

/--
[fkRectMedialDartPrimalLabel_localMate_closed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectMedialPrimalLabel.lean)
-/
@[path]
private lemma fkRectMedialDartPrimalLabel_localMate_closed_eq
  {R : FKRectTorus}
  {d : FKMedialDart R.medialTorus} :
-- imply
  fkRectMedialDartPrimalLabel R (fkMedialLocalMate (fkRectClosedMedialPairing R) d) = fkRectMedialDartPrimalLabel R d := by
-- proof
  apply StatMech.FrontierD.fkRectMedialDartPrimalLabel_localMate_closed R d

/--
[fkRectMedialDartPrimalLabel_localMate_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectMedialPrimalLabel.lean)
-/
@[path]
private lemma fkRectMedialDartPrimalLabel_localMate_reachable_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {d : FKMedialDart R.medialTorus} :
-- imply
  (fkRectOpenGraph R omega).Reachable (fkRectMedialDartPrimalLabel R d) (fkRectMedialDartPrimalLabel R (fkMedialLocalMate (fkRectConfigurationToMedialPairing R omega) d)) := by
-- proof
  apply StatMech.FrontierD.fkRectMedialDartPrimalLabel_localMate_reachable R omega d


-- created on 2026-10-23
