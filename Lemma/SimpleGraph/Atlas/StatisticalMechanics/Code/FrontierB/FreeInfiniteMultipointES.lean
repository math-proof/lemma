import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierB.FreeInfiniteMultipointES
open Filter MeasureTheory Set Topology StatMech StatMech.FrontierB


/--
[openSubgraph_extendEdge_adj_endpoints_mem_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeInfiniteMultipointES.lean)
-/
@[path]
private lemma openSubgraph_extendEdge_adj_endpoints_mem_box_eq
  {d : Nat}
  {n : Nat}
  {omega : ConfigSpace (Sym2 (boxVerts d n))}
  {x y : Site d}
-- given
  (hxy : (openSubgraph d (extendEdge d n omega)).Adj x y) :
-- imply
  x ∈ box d n ∧ y ∈ box d n := by
-- proof
  apply StatMech.FrontierB.openSubgraph_extendEdge_adj_endpoints_mem_box n omega hxy

/--
[openSub_extendEdge_reachable_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeInfiniteMultipointES.lean)
-/
@[path]
private lemma openSub_extendEdge_reachable_iff_eq
  {d : Nat}
  {n : Nat}
  {omega : ConfigSpace (Sym2 (boxVerts d n))}
  {x y : boxVerts d n} :
-- imply
  (openSub (boxGraph d n) omega).Reachable x y ↔ (openSubgraph d (extendEdge d n omega)).Reachable (x : Site d) (y : Site d) := by
-- proof
  apply StatMech.FrontierB.openSub_extendEdge_reachable_iff n omega x y

/--
[markReachableCount_boxSpinSupport_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeInfiniteMultipointES.lean)
-/
@[path]
private lemma markReachableCount_boxSpinSupport_eq_eq
  {d : Nat}
  {n : Nat}
  {omega : ConfigSpace (Sym2 (boxVerts d n))}
  {A : Finset (Site d)}
  {x : boxVerts d n}
-- given
  (hA : (A : Set (Site d)) ⊆ box d n) :
-- imply
  markReachableCount (boxGraph d n) omega (boxSpinSupport d n A) x = markReachableCount (hypercubicLattice d) (extendEdge d n omega) A x := by
-- proof
  apply StatMech.FrontierB.markReachableCount_boxSpinSupport_eq n omega A hA x

/--
[allClustersEven_box_iff_extendEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeInfiniteMultipointES.lean)
-/
@[path]
private lemma allClustersEven_box_iff_extendEdge_eq
  {d : Nat}
  {n : Nat}
  {omega : ConfigSpace (Sym2 (boxVerts d n))}
  {A : Finset (Site d)}
-- given
  (hA : (A : Set (Site d)) ⊆ box d n) :
-- imply
  AllClustersEven (boxGraph d n) omega (boxSpinSupport d n A) ↔ AllClustersEven (hypercubicLattice d) (extendEdge d n omega) A := by
-- proof
  apply StatMech.FrontierB.allClustersEven_box_iff_extendEdge n omega A hA

/--
[boxSpinSupport_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeInfiniteMultipointES.lean)
-/
@[path]
private lemma boxSpinSupport_card_eq
  {d : Nat}
  {n : Nat}
  {A : Finset (Site d)}
-- given
  (hA : (A : Set (Site d)) ⊆ box d n) :
-- imply
  (boxSpinSupport d n A).card = A.card := by
-- proof
  apply StatMech.FrontierB.boxSpinSupport_card n A hA

/--
[freeFiniteMeasure_real_allClustersEvenEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeInfiniteMultipointES.lean)
-/
@[path]
private lemma freeFiniteMeasure_real_allClustersEvenEvent_eq
  {d : Nat}
  {n : Nat}
  {p : Real}
  {A : Finset (Site d)}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hA : (A : Set (Site d)) ⊆ box d n) :
-- imply
  (freeFiniteMeasure d n hp hp1 (by norm_num : (0 : Real) < 2) : Measure _).real (allClustersEvenEvent (hypercubicLattice d) A) = allClustersEvenProb (boxGraph d n) p (boxSpinSupport d n A) := by
-- proof
  apply StatMech.FrontierB.freeFiniteMeasure_real_allClustersEvenEvent n hp hp1 A hA

/--
[integral_freeState_spinProd_eq_freeInfinite_allClustersEven](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeInfiniteMultipointES.lean)
-/
@[path]
private lemma integral_freeState_spinProd_eq_freeInfinite_allClustersEven_eq
  {d : Nat}
  {d : Nat}
  {beta : Real}
  {A : Finset (Site d)}
-- given
  (hbeta : 0 < beta)
  (hd : 1 ≤ d)
  (hAeven : Even A.card) :
-- imply
  (∫ sigma, spinProd A sigma ∂(freeState d beta 0 : Measure (ConfigSpace (Site d)))) = (freeInfiniteVolume d (p := 1 - Real.exp (-2 * beta)) (q := 2) (by apply sub_pos.mpr rw [Real.exp_lt_one_iff] linarith) (by linarith [Real.exp_pos (-2 * beta)]) (by norm_num : (0 : Real) < 2) : Measure _).real (allClustersEvenEvent (hypercubicLattice d) A) := by
-- proof
  apply StatMech.FrontierB.integral_freeState_spinProd_eq_freeInfinite_allClustersEven d beta hbeta hd A hAeven


-- created on 2026-10-23
