import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.FKRectCutFreeLaw
open Finset SimpleGraph StatMech StatMech.FrontierD


/--
[mem_fkRectCutGraph_edgeSet_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCutFreeLaw.lean)
-/
@[path]
private lemma mem_fkRectCutGraph_edgeSet_iff_eq
  {R : FKRectTorus}
  {e : Sym2 R.Vertex} :
-- imply
  e ∈ (fkRectCutGraph R).edgeSet ↔ ∃ a : R.EdgeIndex, a ∉ fkRectTorusCutEdges R ∧ fkRectTorusIndexedEdge R a = e := by
-- proof
  apply StatMech.FrontierD.mem_fkRectCutGraph_edgeSet_iff R e

/--
[fkRectCutClosedEdgeConfigEquiv_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCutFreeLaw.lean)
-/
@[path]
private lemma fkRectCutClosedEdgeConfigEquiv_apply_eq
  {R : FKRectTorus}
  {omega : FKRectCutClosedConfig R} :
-- imply
  (fkRectCutClosedEdgeConfigEquiv R omega).1 = fkRectFullGraphConfiguration R omega.1 := by
-- proof
  apply StatMech.FrontierD.fkRectCutClosedEdgeConfigEquiv_apply R omega

/--
[fkRectCut_openSub_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCutFreeLaw.lean)
-/
@[path]
private lemma fkRectCut_openSub_eq_eq
  {R : FKRectTorus}
  {omega : FKRectCutClosedConfig R} :
-- imply
  FK.openSub (fkRectCutGraph R) (fkRectCutClosedEdgeConfigEquiv R omega).1 = fkRectOpenGraph R omega.1 := by
-- proof
  apply StatMech.FrontierD.fkRectCut_openSub_eq R omega

/--
[fkRectCut_numClusters_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCutFreeLaw.lean)
-/
@[path]
private lemma fkRectCut_numClusters_eq_eq
  {R : FKRectTorus}
  {omega : FKRectCutClosedConfig R} :
-- imply
  FK.numClusters (fkRectCutGraph R) (fkRectCutClosedEdgeConfigEquiv R omega).1 = fkRectNumClusters R omega.1 := by
-- proof
  apply StatMech.FrontierD.fkRectCut_numClusters_eq R omega

/--
[fkOpenCount_eq_openSub_edgeFinset_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCutFreeLaw.lean)
-/
@[path]
private lemma fkOpenCount_eq_openSub_edgeFinset_card_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {omega : ConfigSpace (Sym2 V)} :
-- imply
  FK.openCount G omega = (FK.openSub G omega).edgeFinset.card := by
-- proof
  apply StatMech.FrontierD.fkOpenCount_eq_openSub_edgeFinset_card G omega

/--
[fkRectOpenGraph_edgeFinset_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCutFreeLaw.lean)
-/
@[path]
private lemma fkRectOpenGraph_edgeFinset_card_eq
  {R : FKRectTorus}
  {omega : R.Configuration} :
-- imply
  (fkRectOpenGraph R omega).edgeFinset.card = fkRectOpenEdgeCount R omega := by
-- proof
  apply StatMech.FrontierD.fkRectOpenGraph_edgeFinset_card R omega

/--
[fkRectCut_openCount_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCutFreeLaw.lean)
-/
@[path]
private lemma fkRectCut_openCount_eq_eq
  {R : FKRectTorus}
  {omega : FKRectCutClosedConfig R} :
-- imply
  FK.openCount (fkRectCutGraph R) (fkRectCutClosedEdgeConfigEquiv R omega).1 = fkRectOpenEdgeCount R omega.1 := by
-- proof
  apply StatMech.FrontierD.fkRectCut_openCount_eq R omega

/--
[fkRectCut_edgeProduct_critical_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCutFreeLaw.lean)
-/
@[path]
private lemma fkRectCut_edgeProduct_critical_eq_eq
  {R : FKRectTorus}
  {q : Real}
  {omega : FKRectCutClosedConfig R}
-- given
  (hq : 0 < q) :
-- imply
  FK.edgeProduct (fkRectCutGraph R) (fkRectCriticalP q) (fkRectCutClosedEdgeConfigEquiv R omega).1 = (1 - fkRectCriticalP q) ^ (fkRectCutGraph R).edgeFinset.card * Real.sqrt q ^ fkRectOpenEdgeCount R omega.1 := by
-- proof
  apply StatMech.FrontierD.fkRectCut_edgeProduct_critical_eq R hq omega

/--
[fkRectCut_fkWeight_critical_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCutFreeLaw.lean)
-/
@[path]
private lemma fkRectCut_fkWeight_critical_eq_eq
  {R : FKRectTorus}
  {q : Real}
  {omega : FKRectCutClosedConfig R}
-- given
  (hq : 0 < q) :
-- imply
  FK.fkWeight (fkRectCutGraph R) (fkRectCriticalP q) q (fkRectCutClosedEdgeConfigEquiv R omega).1 = (1 - fkRectCriticalP q) ^ (fkRectCutGraph R).edgeFinset.card * fkRectCriticalReducedWeight R q omega.1 := by
-- proof
  apply StatMech.FrontierD.fkRectCut_fkWeight_critical_eq R hq omega

/--
[fkRectCutClosedReducedEventWeight_univ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCutFreeLaw.lean)
-/
@[path]
private lemma fkRectCutClosedReducedEventWeight_univ_eq
  {R : FKRectTorus}
  {q : Real} :
-- imply
  fkRectCutClosedReducedEventWeight R q Set.univ = fkRectCutClosedReducedZ R q := by
-- proof
  apply StatMech.FrontierD.fkRectCutClosedReducedEventWeight_univ R q

/--
[fkRectCutClosedReducedZ_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCutFreeLaw.lean)
-/
@[path]
private lemma fkRectCutClosedReducedZ_pos_eq
  {R : FKRectTorus}
  {q : Real}
-- given
  (hq : 0 < q) :
-- imply
  0 < fkRectCutClosedReducedZ R q := by
-- proof
  apply StatMech.FrontierD.fkRectCutClosedReducedZ_pos R hq

/--
[fkRect_cutClosed_indicatorReduced_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCutFreeLaw.lean)
-/
@[path]
private lemma fkRect_cutClosed_indicatorReduced_sum_eq
  {R : FKRectTorus}
  {q : Real}
  {A : Set R.Configuration} :
-- imply
  (∑ eta : R.Configuration, {eta | FKRectCutClosedConfiguration R eta ∧ eta ∈ A}.indicator (fun eta => fkRectCriticalReducedWeight R q eta) eta) = fkRectCutClosedReducedEventWeight R q A := by
-- proof
  apply StatMech.FrontierD.fkRect_cutClosed_indicatorReduced_sum R q A

/--
[fkRectCriticalEventMass_cutClosed_inter_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCutFreeLaw.lean)
-/
@[path]
private lemma fkRectCriticalEventMass_cutClosed_inter_eq_eq
  {R : FKRectTorus}
  {q : Real}
  {A : Set R.Configuration} :
-- imply
  fkRectCriticalEventMass R q {eta | FKRectCutClosedConfiguration R eta ∧ eta ∈ A} = fkRectCutClosedReducedEventWeight R q A / fkRectCriticalReducedZ R q := by
-- proof
  apply StatMech.FrontierD.fkRectCriticalEventMass_cutClosed_inter_eq R q A

/--
[fkRectCriticalCutFreeEventMass_eq_reduced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCutFreeLaw.lean)
-/
@[path]
private lemma fkRectCriticalCutFreeEventMass_eq_reduced_eq
  {R : FKRectTorus}
  {q : Real}
  {A : Set R.Configuration}
-- given
  (hq : 1 ≤ q) :
-- imply
  fkRectCriticalCutFreeEventMass R q A = fkRectCutClosedReducedEventWeight R q A / fkRectCutClosedReducedZ R q := by
-- proof
  apply StatMech.FrontierD.fkRectCriticalCutFreeEventMass_eq_reduced R hq A

/--
[fkRectCut_ecz_eventWeight_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCutFreeLaw.lean)
-/
@[path]
private lemma fkRectCut_ecz_eventWeight_eq_eq
  {R : FKRectTorus}
  {q : Real}
  {A : Set R.Configuration}
-- given
  (hq : 0 < q) :
-- imply
  FK.ecz_eventWeight (fkRectCutGraph R) (fkRectCriticalP q) q (fkRectCutEdgeEvent R A) = (1 - fkRectCriticalP q) ^ (fkRectCutGraph R).edgeFinset.card * fkRectCutClosedReducedEventWeight R q A := by
-- proof
  apply StatMech.FrontierD.fkRectCut_ecz_eventWeight_eq R hq A

/--
[fkRectCut_ecz_fkZEdge_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCutFreeLaw.lean)
-/
@[path]
private lemma fkRectCut_ecz_fkZEdge_eq_eq
  {R : FKRectTorus}
  {q : Real}
-- given
  (hq : 0 < q) :
-- imply
  FK.ecz_fkZEdge (fkRectCutGraph R) (fkRectCriticalP q) q = (1 - fkRectCriticalP q) ^ (fkRectCutGraph R).edgeFinset.card * fkRectCutClosedReducedZ R q := by
-- proof
  apply StatMech.FrontierD.fkRectCut_ecz_fkZEdge_eq R hq

/--
[fkRectCriticalCutFreeEventMass_eq_cutGraph](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCutFreeLaw.lean)
-/
@[path]
private lemma fkRectCriticalCutFreeEventMass_eq_cutGraph_eq
  {R : FKRectTorus}
  {q : Real}
  {A : Set R.Configuration}
-- given
  (hq : 1 ≤ q) :
-- imply
  fkRectCriticalCutFreeEventMass R q A = ∑ sigma : ConfigSpace (Sym2 R.Vertex), (FK.ecz_closeOff (fkRectCutGraph R) ⁻¹' fkRectCutEdgeEvent R A).indicator (fun _ => (1 : Real)) sigma * FK.fkProb (fkRectCutGraph R) (fkRectCriticalP q) q sigma := by
-- proof
  apply StatMech.FrontierD.fkRectCriticalCutFreeEventMass_eq_cutGraph R hq A


-- created on 2026-10-23
