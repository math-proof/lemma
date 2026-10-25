import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDevelopedSquare.Part11
open StatMech.Lattice StatMech StatMech.FrontierD


/--
[fkRectSquareSiteVertex_siteOfPair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedSquare.lean)
-/
@[path]
private lemma fkRectSquareSiteVertex_siteOfPair_eq
  {R : FKRectTorus}
  {p : Int × Int} :
-- imply
  fkRectSquareSiteVertex R (fkRectSquareSiteOfPair p) = fkRectSquareRepresentativeVertex R p := by
-- proof
  apply StatMech.FrontierD.fkRectSquareSiteVertex_siteOfPair R p

/--
[fkRectDevelopedSquare_sharedPrimalEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedSquare.lean)
-/
@[path]
private lemma fkRectDevelopedSquare_sharedPrimalEdge_eq
  {n : Nat}
  {f g : Site 2}
-- given
  (hfg : (hypercubicLattice 2).Adj f g) :
-- imply
  sharedPrimalEdge (fkRectDevelopedSquareSite n f) (fkRectDevelopedSquareSite n g) = Sym2.map (fkRectDevelopedSquareSite n) (sharedPrimalEdge f g) := by
-- proof
  apply StatMech.FrontierD.fkRectDevelopedSquare_sharedPrimalEdge n hfg

/--
[fkRectSquareSiteVertex_developedSquareSite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedSquare.lean)
-/
@[path]
private lemma fkRectSquareSiteVertex_developedSquareSite_eq
  {R : FKRectTorus}
  {n : Nat}
  {z : Site 2} :
-- imply
  fkRectSquareSiteVertex R (fkRectDevelopedSquareSite n z) = fkRectDevelopedSquareVertex R n z := by
-- proof
  apply StatMech.FrontierD.fkRectSquareSiteVertex_developedSquareSite R n z

/--
[fkRectDevelopedSquare_undevelop_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedSquare.lean)
-/
@[path]
private lemma fkRectDevelopedSquare_undevelop_bounds_eq
  {R : FKRectTorus}
  {n : Nat}
  {z : Site 2}
-- given
  (hwidth : 3 * n < R.width)
  (hheight : 3 * n < R.height)
  (hz : z ∈ StatMech.RSW.Box.rect 0 n 0 n) :
-- imply
  let p := fkRectSquareUndevelopPoint (fkRectDevelopedSquarePoint n z) 0 ≤ p.1 ∧ p.1 < R.width ∧ 0 ≤ p.2 ∧ p.2 < R.height := by
-- proof
  apply StatMech.FrontierD.fkRectDevelopedSquare_undevelop_bounds R n hwidth hheight hz

/--
[fkRectVertexSquarePoint_developedSquareVertex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedSquare.lean)
-/
@[path]
private lemma fkRectVertexSquarePoint_developedSquareVertex_eq
  {R : FKRectTorus}
  {n : Nat}
  {z : Site 2}
-- given
  (hwidth : 3 * n < R.width)
  (hheight : 3 * n < R.height)
  (hz : z ∈ StatMech.RSW.Box.rect 0 n 0 n) :
-- imply
  fkRectVertexSquarePoint R (fkRectDevelopedSquareVertex R n z) = fkRectDevelopedSquarePoint n z := by
-- proof
  apply StatMech.FrontierD.fkRectVertexSquarePoint_developedSquareVertex R n hwidth hheight hz

/--
[fkRectVertexSquareSite_developedSquareVertex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedSquare.lean)
-/
@[path]
private lemma fkRectVertexSquareSite_developedSquareVertex_eq
  {R : FKRectTorus}
  {n : Nat}
  {z : Site 2}
-- given
  (hwidth : 3 * n < R.width)
  (hheight : 3 * n < R.height)
  (hz : z ∈ StatMech.RSW.Box.rect 0 n 0 n) :
-- imply
  fkRectVertexSquareSite R (fkRectDevelopedSquareVertex R n z) = fkRectDevelopedSquareSite n z := by
-- proof
  apply StatMech.FrontierD.fkRectVertexSquareSite_developedSquareVertex R n hwidth hheight hz

/--
[fkRectDevelopedSquareVertex_fst_succ_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedSquare.lean)
-/
@[path]
private lemma fkRectDevelopedSquareVertex_fst_succ_lt_eq
  {R : FKRectTorus}
  {n : Nat}
  {z : Site 2}
-- given
  (hn : 1 ≤ n)
  (hwidth : 3 * n < R.width)
  (hheight : 3 * n < R.height)
  (hz : z ∈ StatMech.RSW.Box.rect 0 n 0 n) :
-- imply
  (fkRectDevelopedSquareVertex R n z).1.val + 1 < R.width := by
-- proof
  apply StatMech.FrontierD.fkRectDevelopedSquareVertex_fst_succ_lt R n hn hwidth hheight hz

/--
[fkRectDevelopedSquareVertex_injective_on](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedSquare.lean)
-/
@[path]
private lemma fkRectDevelopedSquareVertex_injective_on_eq
  {R : FKRectTorus}
  {n : Nat}
-- given
  (hwidth : 3 * n < R.width)
  (hheight : 3 * n < R.height) :
-- imply
  Set.InjOn (fkRectDevelopedSquareVertex R n) (StatMech.RSW.Box.rect 0 n 0 n) := by
-- proof
  apply StatMech.FrontierD.fkRectDevelopedSquareVertex_injective_on R n hwidth hheight

/--
[fkRectDevelopedSquareVertex_cutGraph_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedSquare.lean)
-/
@[path]
private lemma fkRectDevelopedSquareVertex_cutGraph_adj_eq
  {R : FKRectTorus}
  {n : Nat}
  {z w : Site 2}
-- given
  (hwidth : 3 * n < R.width)
  (hheight : 3 * n < R.height)
  (hz : z ∈ StatMech.RSW.Box.rect 0 n 0 n)
  (hw : w ∈ StatMech.RSW.Box.rect 0 n 0 n)
  (hzw : (hypercubicLattice 2).Adj z w) :
-- imply
  (fkRectCutGraph R).Adj (fkRectDevelopedSquareVertex R n z) (fkRectDevelopedSquareVertex R n w) := by
-- proof
  apply StatMech.FrontierD.fkRectDevelopedSquareVertex_cutGraph_adj R n hwidth hheight hz hw hzw

/--
[fkRectLiftedDualEdge_sharedPrimalEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedSquare.lean)
-/
@[path]
private lemma fkRectLiftedDualEdge_sharedPrimalEdge_eq
  {R : FKRectTorus}
  {e : R.EdgeIndex}
-- given
  (he : e ∉ fkRectTorusCutEdges R)
  (hd : fkRectEdgeToDualEdge R e ∉ fkRectTorusCutEdges R) :
-- imply
  let d := fkRectEdgeToDualEdge R e let df := fkRectLiftedIndexedEdgeEnds R d let ep := fkRectLiftedIndexedEdgeEnds R e sharedPrimalEdge (fkRectSquareSiteOfPair (fkRectSquareDevelopPoint df.1)) (fkRectSquareSiteOfPair (fkRectSquareDevelopPoint df.2)) = Sym2.map fkRectSquareSiteOfPair s(fkRectSquareDevelopPoint ep.1, fkRectSquareDevelopPoint ep.2) := by
-- proof
  apply StatMech.FrontierD.fkRectLiftedDualEdge_sharedPrimalEdge R e he hd

/--
[fkRectDualEdgeToEdge_not_cut_of_developedSquare](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedSquare.lean)
-/
@[path]
private lemma fkRectDualEdgeToEdge_not_cut_of_developedSquare_eq
  {R : FKRectTorus}
  {n : Nat}
  {f g : Site 2}
  {d : R.EdgeIndex}
-- given
  (hn : 1 ≤ n)
  (hwidth : 3 * n < R.width)
  (hheight : 3 * n < R.height)
  (hf : f ∈ StatMech.RSW.Box.rect 0 n 0 n)
  (hg : g ∈ StatMech.RSW.Box.rect 0 n 0 n)
  (hedge : fkRectTorusIndexedEdge R d = s(fkRectDevelopedSquareVertex R n f, fkRectDevelopedSquareVertex R n g))
  (hd : d ∉ fkRectTorusCutEdges R) :
-- imply
  fkRectDualEdgeToEdge R d ∉ fkRectTorusCutEdges R := by
-- proof
  apply StatMech.FrontierD.fkRectDualEdgeToEdge_not_cut_of_developedSquare R n hn hwidth hheight hf hg d hedge hd

/--
[fkRectDevelopedSquarePullback_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedSquare.lean)
-/
@[path]
private lemma fkRectDevelopedSquarePullback_mono_eq
  {R : FKRectTorus}
  {n : Nat}
  {omega tau : R.Configuration}
-- given
  (hot : omega ≤ tau) :
-- imply
  fkRectDevelopedSquarePullback R n omega ≤ fkRectDevelopedSquarePullback R n tau := by
-- proof
  apply StatMech.FrontierD.fkRectDevelopedSquarePullback_mono R n hot

/--
[fkRectDevelopedSquarePullback_open_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedSquare.lean)
-/
@[path]
private lemma fkRectDevelopedSquarePullback_open_iff_eq
  {R : FKRectTorus}
  {n : Nat}
  {omega : R.Configuration}
  {z w : Site 2}
-- given
  (hwidth : 3 * n < R.width)
  (hheight : 3 * n < R.height)
  (hz : z ∈ StatMech.RSW.Box.rect 0 n 0 n)
  (hw : w ∈ StatMech.RSW.Box.rect 0 n 0 n)
  (hzw : (hypercubicLattice 2).Adj z w) :
-- imply
  fkRectDevelopedSquarePullback R n omega s(z, w) = true ↔ (fkRectOpenGraph R omega).Adj (fkRectDevelopedSquareVertex R n z) (fkRectDevelopedSquareVertex R n w) := by
-- proof
  apply StatMech.FrontierD.fkRectDevelopedSquarePullback_open_iff R n hwidth hheight omega hz hw hzw

/--
[fkRectDevelopedSquareHorizontalCrossingEvent_isIncreasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedSquare.lean)
-/
@[path]
private lemma fkRectDevelopedSquareHorizontalCrossingEvent_isIncreasing_eq
  {R : FKRectTorus}
  {n : Nat} :
-- imply
  IsIncreasing (fkRectDevelopedSquareHorizontalCrossingEvent R n) := by
-- proof
  apply StatMech.FrontierD.fkRectDevelopedSquareHorizontalCrossingEvent_isIncreasing R n

/--
[fkRectDevelopedSquare_compl_subset_faceDualVertical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedSquare.lean)
-/
@[path]
private lemma fkRectDevelopedSquare_compl_subset_faceDualVertical_eq
  {R : FKRectTorus}
  {n : Nat}
-- given
  (hn : 1 ≤ n) :
-- imply
  (fkRectDevelopedSquareHorizontalCrossingEvent R n)ᶜ ⊆ fkRectDevelopedSquareFaceDualVerticalEvent R n := by
-- proof
  apply StatMech.FrontierD.fkRectDevelopedSquare_compl_subset_faceDualVertical R n hn

/--
[fkRectDevelopedSquare_faceDual_adj_imp_dual_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedSquare.lean)
-/
@[path]
private lemma fkRectDevelopedSquare_faceDual_adj_imp_dual_adj_eq
  {R : FKRectTorus}
  {n : Nat}
  {omega : R.Configuration}
  {f g : Site 2}
-- given
  (hn : 1 ≤ n)
  (hwidth : 3 * n < R.width)
  (hheight : 3 * n < R.height)
  (hf : f ∈ StatMech.RSW.Box.rect 0 n 0 n)
  (hg : g ∈ StatMech.RSW.Box.rect 0 n 0 n)
  (hfg : (openSubgraph 2 (StatMech.Universality.fci_faceDualConfig (fkRectDevelopedSquarePullback R n omega))).Adj f g) :
-- imply
  (fkRectOpenGraph R (fkRectDualConfigurationEquiv R omega)).Adj (fkRectDevelopedSquareVertex R n f) (fkRectDevelopedSquareVertex R n g) := by
-- proof
  apply StatMech.FrontierD.fkRectDevelopedSquare_faceDual_adj_imp_dual_adj R n hn hwidth hheight omega hf hg hfg

/--
[fkRectDevelopedSquare_faceDualVertical_imp_dualVertical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedSquare.lean)
-/
@[path]
private lemma fkRectDevelopedSquare_faceDualVertical_imp_dualVertical_eq
  {R : FKRectTorus}
  {n : Nat}
  {omega : R.Configuration}
-- given
  (hn : 1 ≤ n)
  (hwidth : 3 * n < R.width)
  (hheight : 3 * n < R.height)
  (hcross : StatMech.RSW.Box.VerticalCrossing (StatMech.Universality.fci_faceDualConfig (fkRectDevelopedSquarePullback R n omega)) 0 n 0 n) :
-- imply
  StatMech.RSW.Box.VerticalCrossing (fkRectDevelopedSquarePullback R n (fkRectDualConfigurationEquiv R omega)) 0 n 0 n := by
-- proof
  apply StatMech.FrontierD.fkRectDevelopedSquare_faceDualVertical_imp_dualVertical R n hn hwidth hheight omega hcross

/--
[fkRectDevelopedSquareVerticalCrossingEvent_isIncreasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedSquare.lean)
-/
@[path]
private lemma fkRectDevelopedSquareVerticalCrossingEvent_isIncreasing_eq
  {R : FKRectTorus}
  {n : Nat} :
-- imply
  IsIncreasing (fkRectDevelopedSquareVerticalCrossingEvent R n) := by
-- proof
  apply StatMech.FrontierD.fkRectDevelopedSquareVerticalCrossingEvent_isIncreasing R n

/--
[fkRectDevelopedSquareCrossingEvent_isIncreasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedSquare.lean)
-/
@[path]
private lemma fkRectDevelopedSquareCrossingEvent_isIncreasing_eq
  {R : FKRectTorus}
  {n : Nat} :
-- imply
  IsIncreasing (fkRectDevelopedSquareCrossingEvent R n) := by
-- proof
  apply StatMech.FrontierD.fkRectDevelopedSquareCrossingEvent_isIncreasing R n

/--
[fkRectDevelopedSquare_dualCompl_subset_crossing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedSquare.lean)
-/
@[path]
private lemma fkRectDevelopedSquare_dualCompl_subset_crossing_eq
  {R : FKRectTorus}
  {n : Nat}
-- given
  (hn : 1 ≤ n)
  (hwidth : 3 * n < R.width)
  (hheight : 3 * n < R.height) :
-- imply
  fkRectDualEvent R (fkRectDevelopedSquareCrossingEvent R n)ᶜ ⊆ fkRectDevelopedSquareCrossingEvent R n := by
-- proof
  apply StatMech.FrontierD.fkRectDevelopedSquare_dualCompl_subset_crossing R n hn hwidth hheight

/--
[fkRectDevelopedSquareCrossing_ge_one_div_one_add_q](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedSquare.lean)
-/
@[path]
private lemma fkRectDevelopedSquareCrossing_ge_one_div_one_add_q_eq
  {R : FKRectTorus}
  {n : Nat}
  {q : Real}
-- given
  (hn : 1 ≤ n)
  (hwidth : 3 * n < R.width)
  (hheight : 3 * n < R.height)
  (hq : 1 ≤ q) :
-- imply
  1 / (1 + q) ≤ fkRectCriticalEventMass R q (fkRectDevelopedSquareCrossingEvent R n) := by
-- proof
  apply StatMech.FrontierD.fkRectDevelopedSquareCrossing_ge_one_div_one_add_q R n hn hwidth hheight hq

/--
[fkRectDevelopedSquare_exists_direction_crossing_ge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedSquare.lean)
-/
@[path]
private lemma fkRectDevelopedSquare_exists_direction_crossing_ge_eq
  {R : FKRectTorus}
  {n : Nat}
  {q : Real}
-- given
  (hn : 1 ≤ n)
  (hwidth : 3 * n < R.width)
  (hheight : 3 * n < R.height)
  (hq : 1 ≤ q) :
-- imply
  1 / (2 * (1 + q)) ≤ fkRectCriticalEventMass R q (fkRectDevelopedSquareHorizontalCrossingEvent R n) ∨ 1 / (2 * (1 + q)) ≤ fkRectCriticalEventMass R q (fkRectDevelopedSquareVerticalCrossingEvent R n) := by
-- proof
  apply StatMech.FrontierD.fkRectDevelopedSquare_exists_direction_crossing_ge R n hn hwidth hheight hq

/--
[mem_fkRectDevelopedSquareHorizontalEndpointPairs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedSquare.lean)
-/
@[path]
private lemma mem_fkRectDevelopedSquareHorizontalEndpointPairs_eq
  {n : Nat}
  {p : (StatMech.RSW.Box.rect 0 n 0 n) × (StatMech.RSW.Box.rect 0 n 0 n)} :
-- imply
  p ∈ fkRectDevelopedSquareHorizontalEndpointPairs n ↔ p.1.1 0 = 0 ∧ p.2.1 0 = n := by
-- proof
  apply StatMech.FrontierD.mem_fkRectDevelopedSquareHorizontalEndpointPairs n p

/--
[mem_fkRectDevelopedSquareVerticalEndpointPairs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedSquare.lean)
-/
@[path]
private lemma mem_fkRectDevelopedSquareVerticalEndpointPairs_eq
  {n : Nat}
  {p : (StatMech.RSW.Box.rect 0 n 0 n) × (StatMech.RSW.Box.rect 0 n 0 n)} :
-- imply
  p ∈ fkRectDevelopedSquareVerticalEndpointPairs n ↔ p.1.1 1 = 0 ∧ p.2.1 1 = n := by
-- proof
  apply StatMech.FrontierD.mem_fkRectDevelopedSquareVerticalEndpointPairs n p

/--
[fkRectDevelopedSquareEndpointConnectionEvent_isIncreasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedSquare.lean)
-/
@[path]
private lemma fkRectDevelopedSquareEndpointConnectionEvent_isIncreasing_eq
  {R : FKRectTorus}
  {n : Nat}
  {p : (StatMech.RSW.Box.rect 0 n 0 n) × (StatMech.RSW.Box.rect 0 n 0 n)} :
-- imply
  IsIncreasing (fkRectDevelopedSquareEndpointConnectionEvent R n p) := by
-- proof
  apply StatMech.FrontierD.fkRectDevelopedSquareEndpointConnectionEvent_isIncreasing R n p

/--
[fkRectDevelopedSquareEndpointConnection_imp_torusReachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedSquare.lean)
-/
@[path]
private lemma fkRectDevelopedSquareEndpointConnection_imp_torusReachable_eq
  {R : FKRectTorus}
  {n : Nat}
  {omega : R.Configuration}
  {p : (StatMech.RSW.Box.rect 0 n 0 n) × (StatMech.RSW.Box.rect 0 n 0 n)}
-- given
  (hwidth : 3 * n < R.width)
  (hheight : 3 * n < R.height)
  (hconn : omega ∈ fkRectDevelopedSquareEndpointConnectionEvent R n p) :
-- imply
  (fkRectOpenGraph R omega).Reachable (fkRectDevelopedSquareVertex R n p.1) (fkRectDevelopedSquareVertex R n p.2) := by
-- proof
  apply StatMech.FrontierD.fkRectDevelopedSquareEndpointConnection_imp_torusReachable R n hwidth hheight omega p hconn

/--
[fkRectDevelopedSquareTorusEndpointConnectionEvent_isIncreasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedSquare.lean)
-/
@[path]
private lemma fkRectDevelopedSquareTorusEndpointConnectionEvent_isIncreasing_eq
  {R : FKRectTorus}
  {n : Nat}
  {p : (StatMech.RSW.Box.rect 0 n 0 n) × (StatMech.RSW.Box.rect 0 n 0 n)} :
-- imply
  IsIncreasing (fkRectDevelopedSquareTorusEndpointConnectionEvent R n p) := by
-- proof
  apply StatMech.FrontierD.fkRectDevelopedSquareTorusEndpointConnectionEvent_isIncreasing R n p

/--
[fkRectDevelopedSquareEndpointConnection_subset_torus](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedSquare.lean)
-/
@[path]
private lemma fkRectDevelopedSquareEndpointConnection_subset_torus_eq
  {R : FKRectTorus}
  {n : Nat}
  {p : (StatMech.RSW.Box.rect 0 n 0 n) × (StatMech.RSW.Box.rect 0 n 0 n)}
-- given
  (hwidth : 3 * n < R.width)
  (hheight : 3 * n < R.height) :
-- imply
  fkRectDevelopedSquareEndpointConnectionEvent R n p ⊆ fkRectDevelopedSquareTorusEndpointConnectionEvent R n p := by
-- proof
  apply StatMech.FrontierD.fkRectDevelopedSquareEndpointConnection_subset_torus R n hwidth hheight p

/--
[fkRectDevelopedSquareHorizontalCrossingEvent_eq_endpointUnion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedSquare.lean)
-/
@[path]
private lemma fkRectDevelopedSquareHorizontalCrossingEvent_eq_endpointUnion_eq
  {R : FKRectTorus}
  {n : Nat} :
-- imply
  fkRectDevelopedSquareHorizontalCrossingEvent R n = fkRectFiniteEventUnion (fkRectDevelopedSquareHorizontalEndpointPairs n) (fkRectDevelopedSquareEndpointConnectionEvent R n) := by
-- proof
  apply StatMech.FrontierD.fkRectDevelopedSquareHorizontalCrossingEvent_eq_endpointUnion R n

/--
[fkRectDevelopedSquareVerticalCrossingEvent_eq_endpointUnion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedSquare.lean)
-/
@[path]
private lemma fkRectDevelopedSquareVerticalCrossingEvent_eq_endpointUnion_eq
  {R : FKRectTorus}
  {n : Nat} :
-- imply
  fkRectDevelopedSquareVerticalCrossingEvent R n = fkRectFiniteEventUnion (fkRectDevelopedSquareVerticalEndpointPairs n) (fkRectDevelopedSquareEndpointConnectionEvent R n) := by
-- proof
  apply StatMech.FrontierD.fkRectDevelopedSquareVerticalCrossingEvent_eq_endpointUnion R n

/--
[fkRectDevelopedSquareHorizontalEndpointPairs_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedSquare.lean)
-/
@[path]
private lemma fkRectDevelopedSquareHorizontalEndpointPairs_nonempty_eq
  {n : Nat} :
-- imply
  (fkRectDevelopedSquareHorizontalEndpointPairs n).Nonempty := by
-- proof
  apply StatMech.FrontierD.fkRectDevelopedSquareHorizontalEndpointPairs_nonempty n

/--
[fkRectDevelopedSquareVerticalEndpointPairs_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedSquare.lean)
-/
@[path]
private lemma fkRectDevelopedSquareVerticalEndpointPairs_nonempty_eq
  {n : Nat} :
-- imply
  (fkRectDevelopedSquareVerticalEndpointPairs n).Nonempty := by
-- proof
  apply StatMech.FrontierD.fkRectDevelopedSquareVerticalEndpointPairs_nonempty n

/--
[fkRectDevelopedSquareHorizontalEndpointPairs_card_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedSquare.lean)
-/
@[path]
private lemma fkRectDevelopedSquareHorizontalEndpointPairs_card_le_eq
  {n : Nat} :
-- imply
  (fkRectDevelopedSquareHorizontalEndpointPairs n).card ≤ (n + 1) ^ 2 := by
-- proof
  apply StatMech.FrontierD.fkRectDevelopedSquareHorizontalEndpointPairs_card_le n

/--
[fkRectDevelopedSquareVerticalEndpointPairs_card_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedSquare.lean)
-/
@[path]
private lemma fkRectDevelopedSquareVerticalEndpointPairs_card_le_eq
  {n : Nat} :
-- imply
  (fkRectDevelopedSquareVerticalEndpointPairs n).card ≤ (n + 1) ^ 2 := by
-- proof
  apply StatMech.FrontierD.fkRectDevelopedSquareVerticalEndpointPairs_card_le n

/--
[fkRectDevelopedSquare_exists_endpoint_connection_ge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedSquare.lean)
-/
@[path]
private lemma fkRectDevelopedSquare_exists_endpoint_connection_ge_eq
  {R : FKRectTorus}
  {n : Nat}
  {q : Real}
-- given
  (hn : 1 ≤ n)
  (hwidth : 3 * n < R.width)
  (hheight : 3 * n < R.height)
  (hq : 1 ≤ q) :
-- imply
  (∃ p ∈ fkRectDevelopedSquareHorizontalEndpointPairs n, 1 / (2 * (1 + q)) ≤ ((fkRectDevelopedSquareHorizontalEndpointPairs n).card : Real) * fkRectCriticalEventMass R q (fkRectDevelopedSquareEndpointConnectionEvent R n p)) ∨ (∃ p ∈ fkRectDevelopedSquareVerticalEndpointPairs n, 1 / (2 * (1 + q)) ≤ ((fkRectDevelopedSquareVerticalEndpointPairs n).card : Real) * fkRectCriticalEventMass R q (fkRectDevelopedSquareEndpointConnectionEvent R n p)) := by
-- proof
  apply StatMech.FrontierD.fkRectDevelopedSquare_exists_endpoint_connection_ge R n hn hwidth hheight hq

/--
[fkRectDevelopedSquare_exists_torus_endpoint_connection_ge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedSquare.lean)
-/
@[path]
private lemma fkRectDevelopedSquare_exists_torus_endpoint_connection_ge_eq
  {R : FKRectTorus}
  {n : Nat}
  {q : Real}
-- given
  (hn : 1 ≤ n)
  (hwidth : 3 * n < R.width)
  (hheight : 3 * n < R.height)
  (hq : 1 ≤ q) :
-- imply
  (∃ p ∈ fkRectDevelopedSquareHorizontalEndpointPairs n, 1 / (2 * (1 + q)) ≤ ((fkRectDevelopedSquareHorizontalEndpointPairs n).card : Real) * fkRectCriticalEventMass R q (fkRectDevelopedSquareTorusEndpointConnectionEvent R n p)) ∨ (∃ p ∈ fkRectDevelopedSquareVerticalEndpointPairs n, 1 / (2 * (1 + q)) ≤ ((fkRectDevelopedSquareVerticalEndpointPairs n).card : Real) * fkRectCriticalEventMass R q (fkRectDevelopedSquareTorusEndpointConnectionEvent R n p)) := by
-- proof
  apply StatMech.FrontierD.fkRectDevelopedSquare_exists_torus_endpoint_connection_ge R n hn hwidth hheight hq

/--
[fkRectDevelopedSquare_exists_torus_endpoint_connection_ge_polynomial](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedSquare.lean)
-/
@[path]
private lemma fkRectDevelopedSquare_exists_torus_endpoint_connection_ge_polynomial_eq
  {R : FKRectTorus}
  {n : Nat}
  {q : Real}
-- given
  (hn : 1 ≤ n)
  (hwidth : 3 * n < R.width)
  (hheight : 3 * n < R.height)
  (hq : 1 ≤ q) :
-- imply
  (∃ p ∈ fkRectDevelopedSquareHorizontalEndpointPairs n, 1 / (2 * (1 + q)) ≤ ((n + 1) ^ 2 : Nat) * fkRectCriticalEventMass R q (fkRectDevelopedSquareTorusEndpointConnectionEvent R n p)) ∨ (∃ p ∈ fkRectDevelopedSquareVerticalEndpointPairs n, 1 / (2 * (1 + q)) ≤ ((n + 1) ^ 2 : Nat) * fkRectCriticalEventMass R q (fkRectDevelopedSquareTorusEndpointConnectionEvent R n p)) := by
-- proof
  apply StatMech.FrontierD.fkRectDevelopedSquare_exists_torus_endpoint_connection_ge_polynomial R n hn hwidth hheight hq

/--
[fkRectDevelopedSquare_exists_torus_endpoint_connection_ge_div](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedSquare.lean)
-/
@[path]
private lemma fkRectDevelopedSquare_exists_torus_endpoint_connection_ge_div_eq
  {R : FKRectTorus}
  {n : Nat}
  {q : Real}
-- given
  (hn : 1 ≤ n)
  (hwidth : 3 * n < R.width)
  (hheight : 3 * n < R.height)
  (hq : 1 ≤ q) :
-- imply
  (∃ p ∈ fkRectDevelopedSquareHorizontalEndpointPairs n, 1 / (2 * (1 + q) * (((n + 1) ^ 2 : Nat) : Real)) ≤ fkRectCriticalEventMass R q (fkRectDevelopedSquareTorusEndpointConnectionEvent R n p)) ∨ (∃ p ∈ fkRectDevelopedSquareVerticalEndpointPairs n, 1 / (2 * (1 + q) * (((n + 1) ^ 2 : Nat) : Real)) ≤ fkRectCriticalEventMass R q (fkRectDevelopedSquareTorusEndpointConnectionEvent R n p)) := by
-- proof
  apply StatMech.FrontierD.fkRectDevelopedSquare_exists_torus_endpoint_connection_ge_div R n hn hwidth hheight hq

/--
[fkRectDevelopedSquare_exists_fkg_attached_torus_endpoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedSquare.lean)
-/
@[path]
private lemma fkRectDevelopedSquare_exists_fkg_attached_torus_endpoint_eq
  {R : FKRectTorus}
  {n : Nat}
  {q : Real}
  {B : Set R.Configuration}
-- given
  (hn : 1 ≤ n)
  (hwidth : 3 * n < R.width)
  (hheight : 3 * n < R.height)
  (hq : 1 ≤ q)
  (hB : IsIncreasing B) :
-- imply
  (∃ p ∈ fkRectDevelopedSquareHorizontalEndpointPairs n, (1 / (2 * (1 + q) * (((n + 1) ^ 2 : Nat) : Real))) * fkRectCriticalEventMass R q B ≤ fkRectCriticalEventMass R q (B ∩ fkRectDevelopedSquareTorusEndpointConnectionEvent R n p)) ∨ (∃ p ∈ fkRectDevelopedSquareVerticalEndpointPairs n, (1 / (2 * (1 + q) * (((n + 1) ^ 2 : Nat) : Real))) * fkRectCriticalEventMass R q B ≤ fkRectCriticalEventMass R q (B ∩ fkRectDevelopedSquareTorusEndpointConnectionEvent R n p)) := by
-- proof
  apply StatMech.FrontierD.fkRectDevelopedSquare_exists_fkg_attached_torus_endpoint R n hn hwidth hheight hq B hB


-- created on 2026-10-23
