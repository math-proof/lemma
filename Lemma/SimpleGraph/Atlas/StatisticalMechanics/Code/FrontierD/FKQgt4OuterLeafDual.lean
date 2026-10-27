import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4OuterLeafDual.Part7
open Finset Set SimpleGraph StatMech StatMech.FrontierD


/--
[pfdOuterFace_infinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4OuterLeafDual.lean)
-/
@[path]
private lemma pfdOuterFace_infinite_eq
  {P : PlanarZ2Subgraph} :
-- imply
  (pfdOuterFace P).supp.Infinite := by
-- proof
  apply StatMech.FrontierD.pfdOuterFace_infinite P

/--
[pfdFace_eq_outer_of_infinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4OuterLeafDual.lean)
-/
@[path]
private lemma pfdFace_eq_outer_of_infinite_eq
  {P : PlanarZ2Subgraph}
  {C : kwg_Face P}
-- given
  (hC : C.supp.Infinite) :
-- imply
  C = pfdOuterFace P := by
-- proof
  apply StatMech.FrontierD.pfdFace_eq_outer_of_infinite P hC

/--
[pfdOuterLeafCollapse_endpoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4OuterLeafDual.lean)
-/
@[path]
private lemma pfdOuterLeafCollapse_endpoint_eq
  {P : PlanarZ2Subgraph}
  {e : kwg_Edge P}
  {side : Bool} :
-- imply
  pfdOuterLeafCollapse P (pfdOuterLeafEndpoint P e side) = pfdOuterLeafSideFace P e side := by
-- proof
  apply StatMech.FrontierD.pfdOuterLeafCollapse_endpoint P e side

/--
[pfdOuterLeafEnds_collapse](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4OuterLeafDual.lean)
-/
@[path]
private lemma pfdOuterLeafEnds_collapse_eq
  {P : PlanarZ2Subgraph}
  {e : kwg_Edge P} :
-- imply
  Sym2.map (pfdOuterLeafCollapse P) (pfdOuterLeafEnds P e) = kwg_dualEnds P e := by
-- proof
  apply StatMech.FrontierD.pfdOuterLeafEnds_collapse P e

/--
[pfdOuterLeafOpenGraph_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4OuterLeafDual.lean)
-/
@[path]
private lemma pfdOuterLeafOpenGraph_adj_eq
  {P : PlanarZ2Subgraph}
  {F : Set (kwg_Edge P)}
  {x y : pfdOuterLeafVertex P} :
-- imply
  (pfdOuterLeafOpenGraph P F).Adj x y ↔ x ≠ y ∧ ∃ e, e ∈ F ∧ pfdOuterLeafEnds P e = s(x, y) := by
-- proof
  apply StatMech.FrontierD.pfdOuterLeafOpenGraph_adj P F x y

/--
[pfdOuterLeafWiredGraph_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4OuterLeafDual.lean)
-/
@[path]
private lemma pfdOuterLeafWiredGraph_adj_eq
  {P : PlanarZ2Subgraph}
  {F : Set (kwg_Edge P)}
  {x y : pfdOuterLeafVertex P} :
-- imply
  (pfdOuterLeafWiredGraph P F).Adj x y ↔ (x ≠ y ∧ ∃ e, e ∈ F ∧ pfdOuterLeafEnds P e = s(x, y)) ∨ (x ≠ y ∧ pfdOuterLeafBoundary P x ∧ pfdOuterLeafBoundary P y) := by
-- proof
  apply StatMech.FrontierD.pfdOuterLeafWiredGraph_adj P F x y

/--
[pfdOuterLeafCollapse_lift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4OuterLeafDual.lean)
-/
@[path]
private lemma pfdOuterLeafCollapse_lift_eq
  {P : PlanarZ2Subgraph}
  {C : kwg_Face P} :
-- imply
  pfdOuterLeafCollapse P (pfdOuterLeafLift P C) = C := by
-- proof
  apply StatMech.FrontierD.pfdOuterLeafCollapse_lift P C

/--
[pfdOuterLeaf_reachable_of_collapse_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4OuterLeafDual.lean)
-/
@[path]
private lemma pfdOuterLeaf_reachable_of_collapse_eq_eq
  {P : PlanarZ2Subgraph}
  {F : Set (kwg_Edge P)}
  {x y : pfdOuterLeafVertex P}
-- given
  (hxy : pfdOuterLeafCollapse P x = pfdOuterLeafCollapse P y) :
-- imply
  (pfdOuterLeafWiredGraph P F).Reachable x y := by
-- proof
  apply StatMech.FrontierD.pfdOuterLeaf_reachable_of_collapse_eq P F hxy

/--
[pfdOuterLeaf_collapse_reachable_of_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4OuterLeafDual.lean)
-/
@[path]
private lemma pfdOuterLeaf_collapse_reachable_of_adj_eq
  {P : PlanarZ2Subgraph}
  {K : SimpleGraph P.V}
  {x y : pfdOuterLeafVertex P}
-- given
  (hxy : (pfdOuterLeafWiredGraph P (pfdOuterLeafClosedEdges P K)).Adj x y) :
-- imply
  (pfdClosedDual P K).Reachable (pfdOuterLeafCollapse P x) (pfdOuterLeafCollapse P y) := by
-- proof
  apply StatMech.FrontierD.pfdOuterLeaf_collapse_reachable_of_adj P K hxy

/--
[pfdOuterLeaf_collapse_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4OuterLeafDual.lean)
-/
@[path]
private lemma pfdOuterLeaf_collapse_reachable_eq
  {P : PlanarZ2Subgraph}
  {K : SimpleGraph P.V}
  {x y : pfdOuterLeafVertex P}
-- given
  (hxy : (pfdOuterLeafWiredGraph P (pfdOuterLeafClosedEdges P K)).Reachable x y) :
-- imply
  (pfdClosedDual P K).Reachable (pfdOuterLeafCollapse P x) (pfdOuterLeafCollapse P y) := by
-- proof
  apply StatMech.FrontierD.pfdOuterLeaf_collapse_reachable P K hxy

/--
[pfdOuterLeaf_reachable_of_dualAdj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4OuterLeafDual.lean)
-/
@[path]
private lemma pfdOuterLeaf_reachable_of_dualAdj_eq
  {P : PlanarZ2Subgraph}
  {K : SimpleGraph P.V}
  {x y : pfdOuterLeafVertex P}
-- given
  (hxy : (pfdClosedDual P K).Adj (pfdOuterLeafCollapse P x) (pfdOuterLeafCollapse P y)) :
-- imply
  (pfdOuterLeafWiredGraph P (pfdOuterLeafClosedEdges P K)).Reachable x y := by
-- proof
  apply StatMech.FrontierD.pfdOuterLeaf_reachable_of_dualAdj P K hxy

/--
[pfdOuterLeaf_lift_reachable_of_dual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4OuterLeafDual.lean)
-/
@[path]
private lemma pfdOuterLeaf_lift_reachable_of_dual_eq
  {P : PlanarZ2Subgraph}
  {K : SimpleGraph P.V}
  {C D : kwg_Face P}
-- given
  (hCD : (pfdClosedDual P K).Reachable C D) :
-- imply
  (pfdOuterLeafWiredGraph P (pfdOuterLeafClosedEdges P K)).Reachable (pfdOuterLeafLift P C) (pfdOuterLeafLift P D) := by
-- proof
  apply StatMech.FrontierD.pfdOuterLeaf_lift_reachable_of_dual P K hCD

/--
[pfdOuterLeaf_reachable_iff_dual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4OuterLeafDual.lean)
-/
@[path]
private lemma pfdOuterLeaf_reachable_iff_dual_eq
  {P : PlanarZ2Subgraph}
  {K : SimpleGraph P.V}
  {x y : pfdOuterLeafVertex P} :
-- imply
  (pfdOuterLeafWiredGraph P (pfdOuterLeafClosedEdges P K)).Reachable x y ↔ (pfdClosedDual P K).Reachable (pfdOuterLeafCollapse P x) (pfdOuterLeafCollapse P y) := by
-- proof
  apply StatMech.FrontierD.pfdOuterLeaf_reachable_iff_dual P K

/--
[pfdOuterLeaf_numClusters_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4OuterLeafDual.lean)
-/
@[path]
private lemma pfdOuterLeaf_numClusters_eq_eq
  {P : PlanarZ2Subgraph}
  {K : SimpleGraph P.V} :
-- imply
  Nat.card (pfdOuterLeafWiredGraph P (pfdOuterLeafClosedEdges P K)).ConnectedComponent = Nat.card (pfdClosedDual P K).ConnectedComponent := by
-- proof
  apply StatMech.FrontierD.pfdOuterLeaf_numClusters_eq P K

/--
[pfdDualWeight_eq_outerLeaf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4OuterLeafDual.lean)
-/
@[path]
private lemma pfdDualWeight_eq_outerLeaf_eq
  {P : PlanarZ2Subgraph}
  {p q : Real}
  {K : SimpleGraph P.V} :
-- imply
  pfdDualWeight P p q K = edgeProductCount p P.G.edgeFinset.card (P.G.edgeFinset.card - K.edgeSet.ncard) * q ^ Nat.card (pfdOuterLeafWiredGraph P (pfdOuterLeafClosedEdges P K)).ConnectedComponent := by
-- proof
  apply StatMech.FrontierD.pfdDualWeight_eq_outerLeaf P p q K

/--
[fkSquareBox_pfdDualWeight_eq_outerLeaf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4OuterLeafDual.lean)
-/
@[path]
private lemma fkSquareBox_pfdDualWeight_eq_outerLeaf_eq
  {n : Nat}
  {p q : Real}
  {K : SimpleGraph (FK.boxVerts 2 n)} :
-- imply
  pfdDualWeight (fkSquareBoxPlanar n) p q K = edgeProductCount p (FK.boxGraph 2 n).edgeFinset.card ((FK.boxGraph 2 n).edgeFinset.card - K.edgeSet.ncard) * q ^ Nat.card (pfdOuterLeafWiredGraph (fkSquareBoxPlanar n) (pfdOuterLeafClosedEdges (fkSquareBoxPlanar n) K)).ConnectedComponent := by
-- proof
  apply StatMech.FrontierD.fkSquareBox_pfdDualWeight_eq_outerLeaf n p q K


-- created on 2026-10-23
