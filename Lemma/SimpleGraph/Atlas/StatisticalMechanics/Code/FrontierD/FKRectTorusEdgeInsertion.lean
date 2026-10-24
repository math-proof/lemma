import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.FKRectTorusEdgeInsertion
open Finset SimpleGraph StatMech StatMech.FrontierD


/--
[fkRectOpenGraph_configurationOfEdges_insert](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusEdgeInsertion.lean)
-/
@[path]
private lemma fkRectOpenGraph_configurationOfEdges_insert_eq
  {R : FKRectTorus}
  {F : Finset R.EdgeIndex}
  {e : R.EdgeIndex}
  {p q : R.Vertex}
-- given
  (he : fkRectTorusIndexedEdge R e = s(p, q)) :
-- imply
  fkRectOpenGraph R (fkRectConfigurationOfEdges R (insert e F)) = fkRectOpenGraph R (fkRectConfigurationOfEdges R F) ⊔ edge p q := by
-- proof
  apply StatMech.FrontierD.fkRectOpenGraph_configurationOfEdges_insert R F e he

/--
[fkRectFinsetClusterCount_insert_of_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusEdgeInsertion.lean)
-/
@[path]
private lemma fkRectFinsetClusterCount_insert_of_reachable_eq
  {R : FKRectTorus}
  {F : Finset R.EdgeIndex}
  {e : R.EdgeIndex}
  {p q : R.Vertex}
-- given
  (he : fkRectTorusIndexedEdge R e = s(p, q))
  (hreach : (fkRectOpenGraph R (fkRectConfigurationOfEdges R F)).Reachable p q) :
-- imply
  fkRectFinsetClusterCount R (insert e F) = fkRectFinsetClusterCount R F := by
-- proof
  apply StatMech.FrontierD.fkRectFinsetClusterCount_insert_of_reachable R F e he hreach

/--
[fkRectFinsetClusterCount_insert_of_not_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusEdgeInsertion.lean)
-/
@[path]
private lemma fkRectFinsetClusterCount_insert_of_not_reachable_eq
  {R : FKRectTorus}
  {F : Finset R.EdgeIndex}
  {e : R.EdgeIndex}
  {p q : R.Vertex}
-- given
  (he : fkRectTorusIndexedEdge R e = s(p, q))
  (hreach : ¬ (fkRectOpenGraph R (fkRectConfigurationOfEdges R F)).Reachable p q) :
-- imply
  fkRectFinsetClusterCount R (insert e F) + 1 = fkRectFinsetClusterCount R F := by
-- proof
  apply StatMech.FrontierD.fkRectFinsetClusterCount_insert_of_not_reachable R F e he hreach


-- created on 2026-10-23
