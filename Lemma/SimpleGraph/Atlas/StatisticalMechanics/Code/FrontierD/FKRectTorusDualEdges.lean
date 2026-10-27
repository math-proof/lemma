import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusDualEdges.Part3
open StatMech StatMech.FrontierD


/--
[fkRectDualEdgeToEdge_edgeToDualEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusDualEdges.lean)
-/
@[path]
private lemma fkRectDualEdgeToEdge_edgeToDualEdge_eq
  {R : FKRectTorus}
  {e : R.EdgeIndex} :
-- imply
  fkRectDualEdgeToEdge R (fkRectEdgeToDualEdge R e) = e := by
-- proof
  apply StatMech.FrontierD.fkRectDualEdgeToEdge_edgeToDualEdge R e

/--
[fkRectEdgeToDualEdge_dualEdgeToEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusDualEdges.lean)
-/
@[path]
private lemma fkRectEdgeToDualEdge_dualEdgeToEdge_eq
  {R : FKRectTorus}
  {e : R.EdgeIndex} :
-- imply
  fkRectEdgeToDualEdge R (fkRectDualEdgeToEdge R e) = e := by
-- proof
  apply StatMech.FrontierD.fkRectEdgeToDualEdge_dualEdgeToEdge R e

/--
[fkRectEdgeDualEquiv_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusDualEdges.lean)
-/
@[path]
private lemma fkRectEdgeDualEquiv_apply_eq
  {R : FKRectTorus}
  {e : R.EdgeIndex} :
-- imply
  fkRectEdgeDualEquiv R e = fkRectEdgeToDualEdge R e := by
-- proof
  apply StatMech.FrontierD.fkRectEdgeDualEquiv_apply R e

/--
[fkRectEdgeDualEquiv_symm_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusDualEdges.lean)
-/
@[path]
private lemma fkRectEdgeDualEquiv_symm_apply_eq
  {R : FKRectTorus}
  {e : R.EdgeIndex} :
-- imply
  (fkRectEdgeDualEquiv R).symm e = fkRectDualEdgeToEdge R e := by
-- proof
  apply StatMech.FrontierD.fkRectEdgeDualEquiv_symm_apply R e

/--
[fkRectDualConfigurationEquiv_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusDualEdges.lean)
-/
@[path]
private lemma fkRectDualConfigurationEquiv_apply_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {e : R.EdgeIndex} :
-- imply
  fkRectDualConfigurationEquiv R omega e = !(omega (fkRectDualEdgeToEdge R e)) := by
-- proof
  apply StatMech.FrontierD.fkRectDualConfigurationEquiv_apply R omega e

/--
[fkRectDualConfigurationEquiv_apply_edgeToDualEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusDualEdges.lean)
-/
@[path]
private lemma fkRectDualConfigurationEquiv_apply_edgeToDualEdge_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {e : R.EdgeIndex} :
-- imply
  fkRectDualConfigurationEquiv R omega (fkRectEdgeToDualEdge R e) = !(omega e) := by
-- proof
  apply StatMech.FrontierD.fkRectDualConfigurationEquiv_apply_edgeToDualEdge R omega e

/--
[fkRectDualConfiguration_open_iff_primal_closed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusDualEdges.lean)
-/
@[path]
private lemma fkRectDualConfiguration_open_iff_primal_closed_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {e : R.EdgeIndex} :
-- imply
  fkRectDualConfigurationEquiv R omega (fkRectEdgeToDualEdge R e) = true ↔ omega e = false := by
-- proof
  apply StatMech.FrontierD.fkRectDualConfiguration_open_iff_primal_closed R omega e

/--
[fkRectDualConfigurationEquiv_antitone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusDualEdges.lean)
-/
@[path]
private lemma fkRectDualConfigurationEquiv_antitone_eq
  {R : FKRectTorus} :
-- imply
  Antitone (fkRectDualConfigurationEquiv R) := by
-- proof
  apply StatMech.FrontierD.fkRectDualConfigurationEquiv_antitone R


-- created on 2026-10-23
