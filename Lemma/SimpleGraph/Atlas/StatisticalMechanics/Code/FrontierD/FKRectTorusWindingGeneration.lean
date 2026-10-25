import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusWindingGeneration
open Finset SimpleGraph StatMech StatMech.FrontierD


/--
[fkRectStepWinding_swap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusWindingGeneration.lean)
-/
@[path]
private lemma fkRectStepWinding_swap_eq
  {R : FKRectTorus}
  {x y : R.Vertex} :
-- imply
  fkRectStepWinding R y x = -fkRectStepWinding R x y := by
-- proof
  apply StatMech.FrontierD.fkRectStepWinding_swap R x y

/--
[fkRectWalkWinding_insert_eq_old_add_zsmul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusWindingGeneration.lean)
-/
@[path]
private lemma fkRectWalkWinding_insert_eq_old_add_zsmul_eq
  {R : FKRectTorus}
  {F : Finset R.EdgeIndex}
  {e : R.EdgeIndex}
  {r : (fkRectOpenGraph R (fkRectConfigurationOfEdges R F)).Walk (fkRectMedialWestPrimal R e) (fkRectMedialEastPrimal R e)}
  {u v : R.Vertex}
  {p : (fkRectOpenGraph R (fkRectConfigurationOfEdges R (insert e F))).Walk u v} :
-- imply
  ∃ q : (fkRectOpenGraph R (fkRectConfigurationOfEdges R F)).Walk u v, ∃ n : Int, fkRectWalkWinding R p = fkRectWalkWinding R q + n • fkRectWalkWinding R (fkRectInsertedFundamentalWalk R F e r) := by
-- proof
  apply StatMech.FrontierD.fkRectWalkWinding_insert_eq_old_add_zsmul R F e r p

/--
[fkRectClosedWindingSubgroup_insert_le_sup_zmultiples](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusWindingGeneration.lean)
-/
@[path]
private lemma fkRectClosedWindingSubgroup_insert_le_sup_zmultiples_eq
  {R : FKRectTorus}
  {F : Finset R.EdgeIndex}
  {e : R.EdgeIndex}
  {r : (fkRectOpenGraph R (fkRectConfigurationOfEdges R F)).Walk (fkRectMedialWestPrimal R e) (fkRectMedialEastPrimal R e)} :
-- imply
  fkRectClosedWindingSubgroup R (fkRectConfigurationOfEdges R (insert e F)) (fkRectMedialWestPrimal R e) ≤ fkRectClosedWindingSubgroup R (fkRectConfigurationOfEdges R F) (fkRectMedialWestPrimal R e) ⊔ AddSubgroup.zmultiples (fkRectWalkWinding R (fkRectInsertedFundamentalWalk R F e r)) := by
-- proof
  apply StatMech.FrontierD.fkRectClosedWindingSubgroup_insert_le_sup_zmultiples R F e r


-- created on 2026-10-23
