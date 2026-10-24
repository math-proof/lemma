import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.FKRectHorizontalCylinderLaw
open Finset SimpleGraph StatMech StatMech.FrontierD


/--
[mem_fkRectHorizontalCutGraphEdges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderLaw.lean)
-/
@[path]
private lemma mem_fkRectHorizontalCutGraphEdges_eq
  {R : FKRectTorus}
  {a : R.EdgeIndex} :
-- imply
  fkRectTorusIndexedEdge R a ∈ fkRectHorizontalCutGraphEdges R ↔ a ∈ fkRectHorizontalCutEdges R := by
-- proof
  apply StatMech.FrontierD.mem_fkRectHorizontalCutGraphEdges R a

/--
[fkRectFullGraphConfiguration_eq_false_of_horizontalCutEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderLaw.lean)
-/
@[path]
private lemma fkRectFullGraphConfiguration_eq_false_of_horizontalCutEdge_eq
  {R : FKRectTorus}
  {eta : FKRectHorizontalCutClosedConfig R}
  {e : Sym2 R.Vertex}
-- given
  (he : e ∈ fkRectHorizontalCutGraphEdges R) :
-- imply
  fkRectFullGraphConfiguration R eta.1 e = false := by
-- proof
  apply StatMech.FrontierD.fkRectFullGraphConfiguration_eq_false_of_horizontalCutEdge R eta he

/--
[fkRectHorizontalCylinderGraph_adj_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderLaw.lean)
-/
@[path]
private lemma fkRectHorizontalCylinderGraph_adj_iff_eq
  {R : FKRectTorus}
  {x y : R.Vertex} :
-- imply
  (fkRectHorizontalCylinderGraph R).Adj x y ↔ (fkRectTorusGraph R).Adj x y ∧ s(x, y) ∉ fkRectHorizontalCutGraphEdges R := by
-- proof
  apply StatMech.FrontierD.fkRectHorizontalCylinderGraph_adj_iff R x y

/--
[mem_fkRectHorizontalCylinderGraph_edgeSet_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderLaw.lean)
-/
@[path]
private lemma mem_fkRectHorizontalCylinderGraph_edgeSet_iff_eq
  {R : FKRectTorus}
  {e : Sym2 R.Vertex} :
-- imply
  e ∈ (fkRectHorizontalCylinderGraph R).edgeSet ↔ ∃ a : R.EdgeIndex, a ∉ fkRectHorizontalCutEdges R ∧ fkRectTorusIndexedEdge R a = e := by
-- proof
  apply StatMech.FrontierD.mem_fkRectHorizontalCylinderGraph_edgeSet_iff R e

/--
[fkRectHorizontalCutClosedEdgeConfigEquiv_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderLaw.lean)
-/
@[path]
private lemma fkRectHorizontalCutClosedEdgeConfigEquiv_apply_eq
  {R : FKRectTorus}
  {omega : FKRectHorizontalCutClosedConfig R} :
-- imply
  (fkRectHorizontalCutClosedEdgeConfigEquiv R omega).1 = fkRectFullGraphConfiguration R omega.1 := by
-- proof
  apply StatMech.FrontierD.fkRectHorizontalCutClosedEdgeConfigEquiv_apply R omega

/--
[fkRectHorizontalCylinder_openSub_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderLaw.lean)
-/
@[path]
private lemma fkRectHorizontalCylinder_openSub_eq_eq
  {R : FKRectTorus}
  {omega : FKRectHorizontalCutClosedConfig R} :
-- imply
  FK.openSub (fkRectHorizontalCylinderGraph R) (fkRectHorizontalCutClosedEdgeConfigEquiv R omega).1 = fkRectOpenGraph R omega.1 := by
-- proof
  apply StatMech.FrontierD.fkRectHorizontalCylinder_openSub_eq R omega

/--
[fkRectHorizontalCylinder_numClusters_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderLaw.lean)
-/
@[path]
private lemma fkRectHorizontalCylinder_numClusters_eq_eq
  {R : FKRectTorus}
  {omega : FKRectHorizontalCutClosedConfig R} :
-- imply
  FK.numClusters (fkRectHorizontalCylinderGraph R) (fkRectHorizontalCutClosedEdgeConfigEquiv R omega).1 = fkRectNumClusters R omega.1 := by
-- proof
  apply StatMech.FrontierD.fkRectHorizontalCylinder_numClusters_eq R omega

/--
[fkRectHorizontalCylinder_openCount_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderLaw.lean)
-/
@[path]
private lemma fkRectHorizontalCylinder_openCount_eq_eq
  {R : FKRectTorus}
  {omega : FKRectHorizontalCutClosedConfig R} :
-- imply
  FK.openCount (fkRectHorizontalCylinderGraph R) (fkRectHorizontalCutClosedEdgeConfigEquiv R omega).1 = fkRectOpenEdgeCount R omega.1 := by
-- proof
  apply StatMech.FrontierD.fkRectHorizontalCylinder_openCount_eq R omega

/--
[fkRectHorizontalCylinder_fkWeight_critical_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderLaw.lean)
-/
@[path]
private lemma fkRectHorizontalCylinder_fkWeight_critical_eq_eq
  {R : FKRectTorus}
  {q : Real}
  {omega : FKRectHorizontalCutClosedConfig R}
-- given
  (hq : 0 < q) :
-- imply
  FK.fkWeight (fkRectHorizontalCylinderGraph R) (fkRectCriticalP q) q (fkRectHorizontalCutClosedEdgeConfigEquiv R omega).1 = (1 - fkRectCriticalP q) ^ (fkRectHorizontalCylinderGraph R).edgeFinset.card * fkRectCriticalReducedWeight R q omega.1 := by
-- proof
  apply StatMech.FrontierD.fkRectHorizontalCylinder_fkWeight_critical_eq R hq omega

/--
[fkRectHorizontalCutClosedReducedEventWeight_univ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderLaw.lean)
-/
@[path]
private lemma fkRectHorizontalCutClosedReducedEventWeight_univ_eq
  {R : FKRectTorus}
  {q : Real} :
-- imply
  fkRectHorizontalCutClosedReducedEventWeight R q Set.univ = fkRectHorizontalCutClosedReducedZ R q := by
-- proof
  apply StatMech.FrontierD.fkRectHorizontalCutClosedReducedEventWeight_univ R q

/--
[fkRectHorizontalCutClosedReducedZ_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderLaw.lean)
-/
@[path]
private lemma fkRectHorizontalCutClosedReducedZ_pos_eq
  {R : FKRectTorus}
  {q : Real}
-- given
  (hq : 0 < q) :
-- imply
  0 < fkRectHorizontalCutClosedReducedZ R q := by
-- proof
  apply StatMech.FrontierD.fkRectHorizontalCutClosedReducedZ_pos R hq

/--
[fkRect_horizontalCutClosed_indicatorReduced_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderLaw.lean)
-/
@[path]
private lemma fkRect_horizontalCutClosed_indicatorReduced_sum_eq
  {R : FKRectTorus}
  {q : Real}
  {A : Set R.Configuration} :
-- imply
  (∑ eta : R.Configuration, {eta | FKRectHorizontalCutClosedConfiguration R eta ∧ eta ∈ A}.indicator (fun eta => fkRectCriticalReducedWeight R q eta) eta) = fkRectHorizontalCutClosedReducedEventWeight R q A := by
-- proof
  apply StatMech.FrontierD.fkRect_horizontalCutClosed_indicatorReduced_sum R q A

/--
[fkRectCriticalEventMass_horizontalCutClosed_inter_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderLaw.lean)
-/
@[path]
private lemma fkRectCriticalEventMass_horizontalCutClosed_inter_eq_eq
  {R : FKRectTorus}
  {q : Real}
  {A : Set R.Configuration} :
-- imply
  fkRectCriticalEventMass R q {eta | FKRectHorizontalCutClosedConfiguration R eta ∧ eta ∈ A} = fkRectHorizontalCutClosedReducedEventWeight R q A / fkRectCriticalReducedZ R q := by
-- proof
  apply StatMech.FrontierD.fkRectCriticalEventMass_horizontalCutClosed_inter_eq R q A

/--
[fkRectCriticalHorizontalCutEventMass_eq_reduced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderLaw.lean)
-/
@[path]
private lemma fkRectCriticalHorizontalCutEventMass_eq_reduced_eq
  {R : FKRectTorus}
  {q : Real}
  {A : Set R.Configuration}
-- given
  (hq : 1 <= q) :
-- imply
  fkRectCriticalHorizontalCutEventMass R q A = fkRectHorizontalCutClosedReducedEventWeight R q A / fkRectHorizontalCutClosedReducedZ R q := by
-- proof
  apply StatMech.FrontierD.fkRectCriticalHorizontalCutEventMass_eq_reduced R hq A

/--
[fkRectHorizontalCylinder_ecz_eventWeight_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderLaw.lean)
-/
@[path]
private lemma fkRectHorizontalCylinder_ecz_eventWeight_eq_eq
  {R : FKRectTorus}
  {q : Real}
  {A : Set R.Configuration}
-- given
  (hq : 0 < q) :
-- imply
  FK.ecz_eventWeight (fkRectHorizontalCylinderGraph R) (fkRectCriticalP q) q (fkRectHorizontalCylinderEdgeEvent R A) = (1 - fkRectCriticalP q) ^ (fkRectHorizontalCylinderGraph R).edgeFinset.card * fkRectHorizontalCutClosedReducedEventWeight R q A := by
-- proof
  apply StatMech.FrontierD.fkRectHorizontalCylinder_ecz_eventWeight_eq R hq A

/--
[fkRectHorizontalCylinder_ecz_fkZEdge_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderLaw.lean)
-/
@[path]
private lemma fkRectHorizontalCylinder_ecz_fkZEdge_eq_eq
  {R : FKRectTorus}
  {q : Real}
-- given
  (hq : 0 < q) :
-- imply
  FK.ecz_fkZEdge (fkRectHorizontalCylinderGraph R) (fkRectCriticalP q) q = (1 - fkRectCriticalP q) ^ (fkRectHorizontalCylinderGraph R).edgeFinset.card * fkRectHorizontalCutClosedReducedZ R q := by
-- proof
  apply StatMech.FrontierD.fkRectHorizontalCylinder_ecz_fkZEdge_eq R hq

/--
[fkRectCriticalHorizontalCutEventMass_eq_cylinderGraph](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderLaw.lean)
-/
@[path]
private lemma fkRectCriticalHorizontalCutEventMass_eq_cylinderGraph_eq
  {R : FKRectTorus}
  {q : Real}
  {A : Set R.Configuration}
-- given
  (hq : 1 <= q) :
-- imply
  fkRectCriticalHorizontalCutEventMass R q A = ∑ sigma : ConfigSpace (Sym2 R.Vertex), (FK.ecz_closeOff (fkRectHorizontalCylinderGraph R) ⁻¹' fkRectHorizontalCylinderEdgeEvent R A).indicator (fun _ => (1 : Real)) sigma * FK.fkProb (fkRectHorizontalCylinderGraph R) (fkRectCriticalP q) q sigma := by
-- proof
  apply StatMech.FrontierD.fkRectCriticalHorizontalCutEventMass_eq_cylinderGraph R hq A


-- created on 2026-10-23
