import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.FKRectTorusEdgeFinset
open Finset SimpleGraph StatMech StatMech.FrontierD


/--
[fkRectConfigurationOfEdges_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusEdgeFinset.lean)
-/
@[path]
private lemma fkRectConfigurationOfEdges_apply_eq
  {R : FKRectTorus}
  {F : Finset R.EdgeIndex}
  {a : R.EdgeIndex} :
-- imply
  fkRectConfigurationOfEdges R F a = true ↔ a ∈ F := by
-- proof
  apply StatMech.FrontierD.fkRectConfigurationOfEdges_apply R F a

/--
[fkRectOpenEdges_configurationOfEdges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusEdgeFinset.lean)
-/
@[path]
private lemma fkRectOpenEdges_configurationOfEdges_eq
  {R : FKRectTorus}
  {F : Finset R.EdgeIndex} :
-- imply
  fkRectOpenEdges R (fkRectConfigurationOfEdges R F) = F := by
-- proof
  apply StatMech.FrontierD.fkRectOpenEdges_configurationOfEdges R F

/--
[fkRectConfigurationOfEdges_openEdges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusEdgeFinset.lean)
-/
@[path]
private lemma fkRectConfigurationOfEdges_openEdges_eq
  {R : FKRectTorus}
  {omega : R.Configuration} :
-- imply
  fkRectConfigurationOfEdges R (fkRectOpenEdges R omega) = omega := by
-- proof
  apply StatMech.FrontierD.fkRectConfigurationOfEdges_openEdges R omega

/--
[fkRectOpenEdgeCount_configurationOfEdges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusEdgeFinset.lean)
-/
@[path]
private lemma fkRectOpenEdgeCount_configurationOfEdges_eq
  {R : FKRectTorus}
  {F : Finset R.EdgeIndex} :
-- imply
  fkRectOpenEdgeCount R (fkRectConfigurationOfEdges R F) = F.card := by
-- proof
  apply StatMech.FrontierD.fkRectOpenEdgeCount_configurationOfEdges R F

/--
[fkRectOpenGraph_configurationOfEdges_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusEdgeFinset.lean)
-/
@[path]
private lemma fkRectOpenGraph_configurationOfEdges_adj_eq
  {R : FKRectTorus}
  {F : Finset R.EdgeIndex}
  {x y : R.Vertex} :
-- imply
  (fkRectOpenGraph R (fkRectConfigurationOfEdges R F)).Adj x y ↔ ∃ a ∈ F, fkRectTorusIndexedEdge R a = s(x, y) := by
-- proof
  apply StatMech.FrontierD.fkRectOpenGraph_configurationOfEdges_adj R F x y

/--
[fkRectOpenGraph_configurationOfEdges_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusEdgeFinset.lean)
-/
@[path]
private lemma fkRectOpenGraph_configurationOfEdges_empty_eq
  {R : FKRectTorus} :
-- imply
  fkRectOpenGraph R (fkRectConfigurationOfEdges R ∅) = ⊥ := by
-- proof
  apply StatMech.FrontierD.fkRectOpenGraph_configurationOfEdges_empty R

/--
[fkRectOpenGraph_configurationOfEdges_univ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusEdgeFinset.lean)
-/
@[path]
private lemma fkRectOpenGraph_configurationOfEdges_univ_eq
  {R : FKRectTorus} :
-- imply
  fkRectOpenGraph R (fkRectConfigurationOfEdges R Finset.univ) = fkRectTorusGraph R := by
-- proof
  apply StatMech.FrontierD.fkRectOpenGraph_configurationOfEdges_univ R

/--
[fkRectFinsetClusterCount_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusEdgeFinset.lean)
-/
@[path]
private lemma fkRectFinsetClusterCount_empty_eq
  {R : FKRectTorus} :
-- imply
  fkRectFinsetClusterCount R ∅ = Fintype.card R.Vertex := by
-- proof
  apply StatMech.FrontierD.fkRectFinsetClusterCount_empty R


-- created on 2026-10-23
