import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectFirstPrimalConnectorInsertion
open SimpleGraph StatMech StatMech.FrontierD


/--
[exists_first_fkRectInsertEdgeList_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectFirstPrimalConnectorInsertion.lean)
-/
@[path]
private lemma exists_first_fkRectInsertEdgeList_reachable_eq
  {R : FKRectTorus}
  {F : Finset R.EdgeIndex}
  {es : List R.EdgeIndex}
  {x y : R.Vertex}
-- given
  (hstart : ¬ (fkRectOpenGraph R (fkRectConfigurationOfEdges R F)).Reachable x y)
  (hfinal : (fkRectOpenGraph R (fkRectConfigurationOfEdges R (fkRectInsertEdgeList R F es))).Reachable x y) :
-- imply
  ∃ pre : List R.EdgeIndex, ∃ e : R.EdgeIndex, ∃ post : List R.EdgeIndex, es = pre ++ e :: post ∧ ¬ (fkRectOpenGraph R (fkRectConfigurationOfEdges R (fkRectInsertEdgeList R F pre))).Reachable x y ∧ (fkRectOpenGraph R (fkRectConfigurationOfEdges R (insert e (fkRectInsertEdgeList R F pre)))).Reachable x y := by
-- proof
  apply StatMech.FrontierD.exists_first_fkRectInsertEdgeList_reachable R F es x y hstart hfinal

/--
[fkRect_firstConnection_fresh_and_medial_not_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectFirstPrimalConnectorInsertion.lean)
-/
@[path]
private lemma fkRect_firstConnection_fresh_and_medial_not_reachable_eq
  {R : FKRectTorus}
  {F : Finset R.EdgeIndex}
  {e : R.EdgeIndex}
  {x y : R.Vertex}
-- given
  (hbefore : ¬ (fkRectOpenGraph R (fkRectConfigurationOfEdges R F)).Reachable x y)
  (hafter : (fkRectOpenGraph R (fkRectConfigurationOfEdges R (insert e F))).Reachable x y) :
-- imply
  e ∉ F ∧ ¬ (fkMedialLoopGraph R.medialTorus (fkRectConfigurationToMedialPairing R (fkRectConfigurationOfEdges R F))).Reachable (fkMedialWestDart (fkRectMedialVertexOfEdge R e)) (fkMedialEastDart (fkRectMedialVertexOfEdge R e)) := by
-- proof
  apply StatMech.FrontierD.fkRect_firstConnection_fresh_and_medial_not_reachable R F e x y hbefore hafter


-- created on 2026-10-23
