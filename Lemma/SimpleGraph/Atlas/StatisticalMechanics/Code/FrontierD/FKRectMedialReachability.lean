import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectMedialReachability
open SimpleGraph StatMech StatMech.FrontierD


/--
[fkRectMedialDartPrimalLabel_west_vertexOfEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectMedialReachability.lean)
-/
@[path]
private lemma fkRectMedialDartPrimalLabel_west_vertexOfEdge_eq
  {R : FKRectTorus}
  {e : R.EdgeIndex} :
-- imply
  fkRectMedialDartPrimalLabel R (fkMedialWestDart (fkRectMedialVertexOfEdge R e)) = fkRectMedialWestPrimal R e := by
-- proof
  apply StatMech.FrontierD.fkRectMedialDartPrimalLabel_west_vertexOfEdge R e

/--
[fkRectMedialDartPrimalLabel_east_vertexOfEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectMedialReachability.lean)
-/
@[path]
private lemma fkRectMedialDartPrimalLabel_east_vertexOfEdge_eq
  {R : FKRectTorus}
  {e : R.EdgeIndex} :
-- imply
  fkRectMedialDartPrimalLabel R (fkMedialEastDart (fkRectMedialVertexOfEdge R e)) = fkRectMedialEastPrimal R e := by
-- proof
  apply StatMech.FrontierD.fkRectMedialDartPrimalLabel_east_vertexOfEdge R e

/--
[fkRectMedial_adj_primalLabel_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectMedialReachability.lean)
-/
@[path]
private lemma fkRectMedial_adj_primalLabel_reachable_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {d e : FKMedialDart R.medialTorus}
-- given
  (hde : (fkMedialLoopGraph R.medialTorus (fkRectConfigurationToMedialPairing R omega)).Adj d e) :
-- imply
  (fkRectOpenGraph R omega).Reachable (fkRectMedialDartPrimalLabel R d) (fkRectMedialDartPrimalLabel R e) := by
-- proof
  apply StatMech.FrontierD.fkRectMedial_adj_primalLabel_reachable R omega hde

/--
[fkRectMedial_reachable_primalLabel_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectMedialReachability.lean)
-/
@[path]
private lemma fkRectMedial_reachable_primalLabel_reachable_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {d e : FKMedialDart R.medialTorus}
-- given
  (hde : (fkMedialLoopGraph R.medialTorus (fkRectConfigurationToMedialPairing R omega)).Reachable d e) :
-- imply
  (fkRectOpenGraph R omega).Reachable (fkRectMedialDartPrimalLabel R d) (fkRectMedialDartPrimalLabel R e) := by
-- proof
  apply StatMech.FrontierD.fkRectMedial_reachable_primalLabel_reachable R omega hde

/--
[fkRectMedial_west_east_not_reachable_of_endpoints](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectMedialReachability.lean)
-/
@[path]
private lemma fkRectMedial_west_east_not_reachable_of_endpoints_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {e : R.EdgeIndex}
  {p q : R.Vertex}
-- given
  (hedge : fkRectTorusIndexedEdge R e = s(p, q))
  (hpq : ¬ (fkRectOpenGraph R omega).Reachable p q) :
-- imply
  ¬ (fkMedialLoopGraph R.medialTorus (fkRectConfigurationToMedialPairing R omega)).Reachable (fkMedialWestDart (fkRectMedialVertexOfEdge R e)) (fkMedialEastDart (fkRectMedialVertexOfEdge R e)) := by
-- proof
  apply StatMech.FrontierD.fkRectMedial_west_east_not_reachable_of_endpoints R omega e hedge hpq


-- created on 2026-10-23
