import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectFirstEssentialInsertion
open SimpleGraph StatMech StatMech.FrontierD


/--
[fkRectFirstEssentialInsertion_newBoundaryOrbit_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectFirstEssentialInsertion.lean)
-/
@[path]
private lemma fkRectFirstEssentialInsertion_newBoundaryOrbit_ne_zero_eq
  {R : FKRectTorus}
  {F : Finset R.EdgeIndex}
  {e : R.EdgeIndex}
  {r : (fkRectOpenGraph R (fkRectConfigurationOfEdges R F)).Walk (fkRectMedialWestPrimal R e) (fkRectMedialEastPrimal R e)}
-- given
  (heF : e ∉ F)
  (hold : ¬ FKRectHasNet R (fkRectConfigurationOfEdges R F))
  (htrivial : ∀ (x : R.Vertex) (p : (fkRectOpenGraph R (fkRectConfigurationOfEdges R F)).Walk x x), fkRectWalkWinding R p = (0, 0))
  (hfund : fkRectWalkWinding R (fkRectInsertedFundamentalWalk R F e r) ≠ (0, 0)) :
-- imply
  fkRectWalkWinding R (fkRectMedialBoundaryPrimalOrbitWalk R (fkRectConfigurationOfEdges R (insert e F)) (fkMedialBlackDart0 (fkRectMedialVertexOfEdge R e)).1) ≠ (0, 0) := by
-- proof
  apply StatMech.FrontierD.fkRectFirstEssentialInsertion_newBoundaryOrbit_ne_zero R F e r heF hold htrivial hfund


-- created on 2026-10-23
