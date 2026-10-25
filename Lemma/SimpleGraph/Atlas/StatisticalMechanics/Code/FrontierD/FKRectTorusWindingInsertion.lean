import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusWindingInsertion.Part2
open Finset SimpleGraph StatMech StatMech.FrontierD


/--
[fkRectClosedWindingSubgroup_mono_configurationOfEdges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusWindingInsertion.lean)
-/
@[path]
private lemma fkRectClosedWindingSubgroup_mono_configurationOfEdges_eq
  {R : FKRectTorus}
  {F A : Finset R.EdgeIndex}
  {x : R.Vertex}
-- given
  (hFA : F ⊆ A) :
-- imply
  fkRectClosedWindingSubgroup R (fkRectConfigurationOfEdges R F) x ≤ fkRectClosedWindingSubgroup R (fkRectConfigurationOfEdges R A) x := by
-- proof
  apply StatMech.FrontierD.fkRectClosedWindingSubgroup_mono_configurationOfEdges R hFA x

/--
[fkRectOpenGraph_le_insert](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusWindingInsertion.lean)
-/
@[path]
private lemma fkRectOpenGraph_le_insert_eq
  {R : FKRectTorus}
  {F : Finset R.EdgeIndex}
  {e : R.EdgeIndex} :
-- imply
  fkRectOpenGraph R (fkRectConfigurationOfEdges R F) ≤ fkRectOpenGraph R (fkRectConfigurationOfEdges R (insert e F)) := by
-- proof
  apply StatMech.FrontierD.fkRectOpenGraph_le_insert R F e

/--
[fkRectOpenGraph_insert_adj_medialPrimals](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusWindingInsertion.lean)
-/
@[path]
private lemma fkRectOpenGraph_insert_adj_medialPrimals_eq
  {R : FKRectTorus}
  {F : Finset R.EdgeIndex}
  {e : R.EdgeIndex} :
-- imply
  (fkRectOpenGraph R (fkRectConfigurationOfEdges R (insert e F))).Adj (fkRectMedialEastPrimal R e) (fkRectMedialWestPrimal R e) := by
-- proof
  apply StatMech.FrontierD.fkRectOpenGraph_insert_adj_medialPrimals R F e

/--
[fkRectInsertedFundamentalWalk_winding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusWindingInsertion.lean)
-/
@[path]
private lemma fkRectInsertedFundamentalWalk_winding_eq
  {R : FKRectTorus}
  {F : Finset R.EdgeIndex}
  {e : R.EdgeIndex}
  {p : (fkRectOpenGraph R (fkRectConfigurationOfEdges R F)).Walk (fkRectMedialWestPrimal R e) (fkRectMedialEastPrimal R e)} :
-- imply
  fkRectWalkWinding R (fkRectInsertedFundamentalWalk R F e p) = ((fkRectWalkWinding R p).1 + fkRectHorizontalSeamIncrement R (fkRectMedialEastPrimal R e) (fkRectMedialWestPrimal R e), (fkRectWalkWinding R p).2 + fkRectVerticalSeamIncrement R (fkRectMedialEastPrimal R e) (fkRectMedialWestPrimal R e)) := by
-- proof
  apply StatMech.FrontierD.fkRectInsertedFundamentalWalk_winding R F e p

/--
[FKRectHasNet_insert_of_independent_fundamentalWalk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusWindingInsertion.lean)
-/
@[path]
private lemma FKRectHasNet_insert_of_independent_fundamentalWalk_eq
  {R : FKRectTorus}
  {F : Finset R.EdgeIndex}
  {e : R.EdgeIndex}
  {p : (fkRectOpenGraph R (fkRectConfigurationOfEdges R F)).Walk (fkRectMedialWestPrimal R e) (fkRectMedialEastPrimal R e)}
  {q : (fkRectOpenGraph R (fkRectConfigurationOfEdges R F)).Walk (fkRectMedialWestPrimal R e) (fkRectMedialWestPrimal R e)}
-- given
  (hind : FKRectWindingIndependent (fkRectWalkWinding R q) ((fkRectWalkWinding R p).1 + fkRectHorizontalSeamIncrement R (fkRectMedialEastPrimal R e) (fkRectMedialWestPrimal R e), (fkRectWalkWinding R p).2 + fkRectVerticalSeamIncrement R (fkRectMedialEastPrimal R e) (fkRectMedialWestPrimal R e))) :
-- imply
  FKRectHasNet R (fkRectConfigurationOfEdges R (insert e F)) := by
-- proof
  apply StatMech.FrontierD.FKRectHasNet_insert_of_independent_fundamentalWalk R F e p q hind


-- created on 2026-10-23
