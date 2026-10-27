import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusDisconnectedInsertion.Part2
open SimpleGraph StatMech StatMech.FrontierD


/--
[fkRectWalkWinding_concat_eq_add_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusDisconnectedInsertion.lean)
-/
@[path]
private lemma fkRectWalkWinding_concat_eq_add_step_eq
  {R : FKRectTorus}
  {G : SimpleGraph R.Vertex}
  {x y z : R.Vertex}
  {p : G.Walk x y}
-- given
  (h : G.Adj y z) :
-- imply
  fkRectWalkWinding R (p.concat h) = fkRectWalkWinding R p + fkRectStepWinding R y z := by
-- proof
  apply StatMech.FrontierD.fkRectWalkWinding_concat_eq_add_step R p h

/--
[fkRectWalkWinding_sup_edge_decomposition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusDisconnectedInsertion.lean)
-/
@[path]
private lemma fkRectWalkWinding_sup_edge_decomposition_eq
  {R : FKRectTorus}
  {G : SimpleGraph R.Vertex}
  {a b : R.Vertex}
  {y : R.Vertex}
  {p : (G ⊔ SimpleGraph.edge a b).Walk a y}
-- given
  (hab : ¬ G.Reachable a b) :
-- imply
  (∃ q : G.Walk a y, fkRectWalkWinding R p - fkRectWalkWinding R q ∈ fkRectGraphClosedWindingSubgroup R G a ⊔ fkRectGraphClosedWindingSubgroup R G b) ∨ (∃ q : G.Walk b y, fkRectWalkWinding R p - fkRectStepWinding R a b - fkRectWalkWinding R q ∈ fkRectGraphClosedWindingSubgroup R G a ⊔ fkRectGraphClosedWindingSubgroup R G b) := by
-- proof
  apply StatMech.FrontierD.fkRectWalkWinding_sup_edge_decomposition R G a b hab p

/--
[fkRectGraphClosedWindingSubgroup_sup_edge_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusDisconnectedInsertion.lean)
-/
@[path]
private lemma fkRectGraphClosedWindingSubgroup_sup_edge_eq_eq
  {R : FKRectTorus}
  {G : SimpleGraph R.Vertex}
  {a b : R.Vertex}
-- given
  (hab : ¬ G.Reachable a b) :
-- imply
  fkRectGraphClosedWindingSubgroup R (G ⊔ SimpleGraph.edge a b) a = fkRectGraphClosedWindingSubgroup R G a ⊔ fkRectGraphClosedWindingSubgroup R G b := by
-- proof
  apply StatMech.FrontierD.fkRectGraphClosedWindingSubgroup_sup_edge_eq R G a b hab

/--
[fkRectGraphClosedWindingSubgroup_openGraph](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusDisconnectedInsertion.lean)
-/
@[path]
private lemma fkRectGraphClosedWindingSubgroup_openGraph_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {x : R.Vertex} :
-- imply
  fkRectGraphClosedWindingSubgroup R (fkRectOpenGraph R omega) x = fkRectClosedWindingSubgroup R omega x := by
-- proof
  apply StatMech.FrontierD.fkRectGraphClosedWindingSubgroup_openGraph R omega x

/--
[fkRectClosedWindingSubgroup_insert_eq_sup_of_not_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusDisconnectedInsertion.lean)
-/
@[path]
private lemma fkRectClosedWindingSubgroup_insert_eq_sup_of_not_reachable_eq
  {R : FKRectTorus}
  {F : Finset R.EdgeIndex}
  {e : R.EdgeIndex}
-- given
  (hdisc : ¬ (fkRectOpenGraph R (fkRectConfigurationOfEdges R F)).Reachable (fkRectMedialWestPrimal R e) (fkRectMedialEastPrimal R e)) :
-- imply
  fkRectClosedWindingSubgroup R (fkRectConfigurationOfEdges R (insert e F)) (fkRectMedialWestPrimal R e) = fkRectClosedWindingSubgroup R (fkRectConfigurationOfEdges R F) (fkRectMedialWestPrimal R e) ⊔ fkRectClosedWindingSubgroup R (fkRectConfigurationOfEdges R F) (fkRectMedialEastPrimal R e) := by
-- proof
  apply StatMech.FrontierD.fkRectClosedWindingSubgroup_insert_eq_sup_of_not_reachable R F e hdisc

/--
[fkRectWalkWinding_sup_edge_eq_old_of_not_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusDisconnectedInsertion.lean)
-/
@[path]
private lemma fkRectWalkWinding_sup_edge_eq_old_of_not_reachable_eq
  {R : FKRectTorus}
  {G : SimpleGraph R.Vertex}
  {a b : R.Vertex}
  {x y : R.Vertex}
  {p : (G ⊔ SimpleGraph.edge a b).Walk x y}
-- given
  (hxa : ¬ G.Reachable x a)
  (hxb : ¬ G.Reachable x b) :
-- imply
  ∃ q : G.Walk x y, fkRectWalkWinding R p = fkRectWalkWinding R q := by
-- proof
  apply StatMech.FrontierD.fkRectWalkWinding_sup_edge_eq_old_of_not_reachable R G a b hxa hxb p

/--
[fkRectGraphClosedWindingSubgroup_sup_edge_eq_of_away](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusDisconnectedInsertion.lean)
-/
@[path]
private lemma fkRectGraphClosedWindingSubgroup_sup_edge_eq_of_away_eq
  {R : FKRectTorus}
  {G : SimpleGraph R.Vertex}
  {a b x : R.Vertex}
-- given
  (hxa : ¬ G.Reachable x a)
  (hxb : ¬ G.Reachable x b) :
-- imply
  fkRectGraphClosedWindingSubgroup R (G ⊔ SimpleGraph.edge a b) x = fkRectGraphClosedWindingSubgroup R G x := by
-- proof
  apply StatMech.FrontierD.fkRectGraphClosedWindingSubgroup_sup_edge_eq_of_away R G a b x hxa hxb

/--
[fkRectClosedWindingSubgroup_insert_eq_of_away](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusDisconnectedInsertion.lean)
-/
@[path]
private lemma fkRectClosedWindingSubgroup_insert_eq_of_away_eq
  {R : FKRectTorus}
  {F : Finset R.EdgeIndex}
  {e : R.EdgeIndex}
  {x : R.Vertex}
-- given
  (hxa : ¬ (fkRectOpenGraph R (fkRectConfigurationOfEdges R F)).Reachable x (fkRectMedialWestPrimal R e))
  (hxb : ¬ (fkRectOpenGraph R (fkRectConfigurationOfEdges R F)).Reachable x (fkRectMedialEastPrimal R e)) :
-- imply
  fkRectClosedWindingSubgroup R (fkRectConfigurationOfEdges R (insert e F)) x = fkRectClosedWindingSubgroup R (fkRectConfigurationOfEdges R F) x := by
-- proof
  apply StatMech.FrontierD.fkRectClosedWindingSubgroup_insert_eq_of_away R F e x hxa hxb

/--
[not_fkRectHasNet_insert_of_not_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusDisconnectedInsertion.lean)
-/
@[path]
private lemma not_fkRectHasNet_insert_of_not_reachable_eq
  {R : FKRectTorus}
  {F : Finset R.EdgeIndex}
  {e : R.EdgeIndex}
-- given
  (hold : ¬ FKRectHasNet R (fkRectConfigurationOfEdges R F))
  (hdisc : ¬ (fkRectOpenGraph R (fkRectConfigurationOfEdges R F)).Reachable (fkRectMedialWestPrimal R e) (fkRectMedialEastPrimal R e)) :
-- imply
  ¬ FKRectHasNet R (fkRectConfigurationOfEdges R (insert e F)) := by
-- proof
  apply StatMech.FrontierD.not_fkRectHasNet_insert_of_not_reachable R F e hold hdisc

/--
[fkRectHasNet_insert_iff_of_not_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusDisconnectedInsertion.lean)
-/
@[path]
private lemma fkRectHasNet_insert_iff_of_not_reachable_eq
  {R : FKRectTorus}
  {F : Finset R.EdgeIndex}
  {e : R.EdgeIndex}
-- given
  (hdisc : ¬ (fkRectOpenGraph R (fkRectConfigurationOfEdges R F)).Reachable (fkRectMedialWestPrimal R e) (fkRectMedialEastPrimal R e)) :
-- imply
  FKRectHasNet R (fkRectConfigurationOfEdges R (insert e F)) ↔ FKRectHasNet R (fkRectConfigurationOfEdges R F) := by
-- proof
  apply StatMech.FrontierD.fkRectHasNet_insert_iff_of_not_reachable R F e hdisc


-- created on 2026-10-23
