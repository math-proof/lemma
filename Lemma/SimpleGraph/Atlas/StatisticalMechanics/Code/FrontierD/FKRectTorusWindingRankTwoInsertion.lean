import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusWindingRankTwoInsertion
open Finset SimpleGraph StatMech StatMech.FrontierD


/--
[fkRectClosedWindingSubgroup_insert_eq_sup_zmultiples](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusWindingRankTwoInsertion.lean)
-/
@[path]
private lemma fkRectClosedWindingSubgroup_insert_eq_sup_zmultiples_eq
  {R : FKRectTorus}
  {F : Finset R.EdgeIndex}
  {e : R.EdgeIndex}
  {r : (fkRectOpenGraph R (fkRectConfigurationOfEdges R F)).Walk (fkRectMedialWestPrimal R e) (fkRectMedialEastPrimal R e)} :
-- imply
  fkRectClosedWindingSubgroup R (fkRectConfigurationOfEdges R (insert e F)) (fkRectMedialWestPrimal R e) = fkRectClosedWindingSubgroup R (fkRectConfigurationOfEdges R F) (fkRectMedialWestPrimal R e) ⊔ AddSubgroup.zmultiples (fkRectWalkWinding R (fkRectInsertedFundamentalWalk R F e r)) := by
-- proof
  apply StatMech.FrontierD.fkRectClosedWindingSubgroup_insert_eq_sup_zmultiples R F e r

/--
[windingRankTwo_sup_zmultiples_iff_of_not_rankTwo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusWindingRankTwoInsertion.lean)
-/
@[path]
private lemma windingRankTwo_sup_zmultiples_iff_of_not_rankTwo_eq
  {H : AddSubgroup (Int × Int)}
  {v : Int × Int}
-- given
  (hH : ¬ ∃ x ∈ H, ∃ y ∈ H, FKRectWindingIndependent x y) :
-- imply
  (∃ a ∈ H ⊔ AddSubgroup.zmultiples v, ∃ b ∈ H ⊔ AddSubgroup.zmultiples v, FKRectWindingIndependent a b) ↔ ∃ x ∈ H, FKRectWindingIndependent x v := by
-- proof
  apply StatMech.FrontierD.windingRankTwo_sup_zmultiples_iff_of_not_rankTwo H v hH

/--
[fkRectWindingSubgroupRankTwo_insert_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusWindingRankTwoInsertion.lean)
-/
@[path]
private lemma fkRectWindingSubgroupRankTwo_insert_iff_eq
  {R : FKRectTorus}
  {F : Finset R.EdgeIndex}
  {e : R.EdgeIndex}
  {r : (fkRectOpenGraph R (fkRectConfigurationOfEdges R F)).Walk (fkRectMedialWestPrimal R e) (fkRectMedialEastPrimal R e)}
-- given
  (hold : ¬ FKRectWindingSubgroupRankTwo R (fkRectConfigurationOfEdges R F) (fkRectMedialWestPrimal R e)) :
-- imply
  FKRectWindingSubgroupRankTwo R (fkRectConfigurationOfEdges R (insert e F)) (fkRectMedialWestPrimal R e) ↔ ∃ q : (fkRectOpenGraph R (fkRectConfigurationOfEdges R F)).Walk (fkRectMedialWestPrimal R e) (fkRectMedialWestPrimal R e), FKRectWindingIndependent (fkRectWalkWinding R q) (fkRectWalkWinding R (fkRectInsertedFundamentalWalk R F e r)) := by
-- proof
  apply StatMech.FrontierD.fkRectWindingSubgroupRankTwo_insert_iff R F e r hold

/--
[fkRectWalkWinding_insert_eq_old_of_not_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusWindingRankTwoInsertion.lean)
-/
@[path]
private lemma fkRectWalkWinding_insert_eq_old_of_not_reachable_eq
  {R : FKRectTorus}
  {F : Finset R.EdgeIndex}
  {e : R.EdgeIndex}
  {r : (fkRectOpenGraph R (fkRectConfigurationOfEdges R F)).Walk (fkRectMedialWestPrimal R e) (fkRectMedialEastPrimal R e)}
  {x y : R.Vertex}
  {p : (fkRectOpenGraph R (fkRectConfigurationOfEdges R (insert e F))).Walk x y}
-- given
  (hxa : ¬ (fkRectOpenGraph R (fkRectConfigurationOfEdges R F)).Reachable x (fkRectMedialWestPrimal R e)) :
-- imply
  ∃ q : (fkRectOpenGraph R (fkRectConfigurationOfEdges R F)).Walk x y, fkRectWalkWinding R p = fkRectWalkWinding R q := by
-- proof
  apply StatMech.FrontierD.fkRectWalkWinding_insert_eq_old_of_not_reachable R F e r hxa p

/--
[fkRectClosedWindingSubgroup_insert_eq_of_not_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusWindingRankTwoInsertion.lean)
-/
@[path]
private lemma fkRectClosedWindingSubgroup_insert_eq_of_not_reachable_eq
  {R : FKRectTorus}
  {F : Finset R.EdgeIndex}
  {e : R.EdgeIndex}
  {r : (fkRectOpenGraph R (fkRectConfigurationOfEdges R F)).Walk (fkRectMedialWestPrimal R e) (fkRectMedialEastPrimal R e)}
  {x : R.Vertex}
-- given
  (hxa : ¬ (fkRectOpenGraph R (fkRectConfigurationOfEdges R F)).Reachable x (fkRectMedialWestPrimal R e)) :
-- imply
  fkRectClosedWindingSubgroup R (fkRectConfigurationOfEdges R (insert e F)) x = fkRectClosedWindingSubgroup R (fkRectConfigurationOfEdges R F) x := by
-- proof
  apply StatMech.FrontierD.fkRectClosedWindingSubgroup_insert_eq_of_not_reachable R F e r x hxa

/--
[fkRectHasNet_insert_iff_rankTwo_at_endpoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusWindingRankTwoInsertion.lean)
-/
@[path]
private lemma fkRectHasNet_insert_iff_rankTwo_at_endpoint_eq
  {R : FKRectTorus}
  {F : Finset R.EdgeIndex}
  {e : R.EdgeIndex}
  {r : (fkRectOpenGraph R (fkRectConfigurationOfEdges R F)).Walk (fkRectMedialWestPrimal R e) (fkRectMedialEastPrimal R e)}
-- given
  (hold : ¬ FKRectHasNet R (fkRectConfigurationOfEdges R F)) :
-- imply
  FKRectHasNet R (fkRectConfigurationOfEdges R (insert e F)) ↔ FKRectWindingSubgroupRankTwo R (fkRectConfigurationOfEdges R (insert e F)) (fkRectMedialWestPrimal R e) := by
-- proof
  apply StatMech.FrontierD.fkRectHasNet_insert_iff_rankTwo_at_endpoint R F e r hold

/--
[fkRectHasNet_insert_iff_exists_independent_fundamentalWalk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusWindingRankTwoInsertion.lean)
-/
@[path]
private lemma fkRectHasNet_insert_iff_exists_independent_fundamentalWalk_eq
  {R : FKRectTorus}
  {F : Finset R.EdgeIndex}
  {e : R.EdgeIndex}
  {r : (fkRectOpenGraph R (fkRectConfigurationOfEdges R F)).Walk (fkRectMedialWestPrimal R e) (fkRectMedialEastPrimal R e)}
-- given
  (hold : ¬ FKRectHasNet R (fkRectConfigurationOfEdges R F)) :
-- imply
  FKRectHasNet R (fkRectConfigurationOfEdges R (insert e F)) ↔ ∃ q : (fkRectOpenGraph R (fkRectConfigurationOfEdges R F)).Walk (fkRectMedialWestPrimal R e) (fkRectMedialWestPrimal R e), FKRectWindingIndependent (fkRectWalkWinding R q) (fkRectWalkWinding R (fkRectInsertedFundamentalWalk R F e r)) := by
-- proof
  apply StatMech.FrontierD.fkRectHasNet_insert_iff_exists_independent_fundamentalWalk R F e r hold


-- created on 2026-10-23
