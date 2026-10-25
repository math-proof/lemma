import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.DualCircuitToWalk.Part4
open Set SimpleGraph StatMech.Lattice StatMech.RSW.Box StatMech StatMech.Universality


/--
[dcw_barrier_closed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/DualCircuitToWalk.lean)
-/
@[path]
private lemma dcw_barrier_closed_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {v w : Site 2}
-- given
  (h : dcw_isBarrierEdge ω n v w) :
-- imply
  ω s(v, w) = false := by
-- proof
  apply StatMech.Universality.dcw_barrier_closed ω n h

/--
[dcw_barrier_dual_open](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/DualCircuitToWalk.lean)
-/
@[path]
private lemma dcw_barrier_dual_open_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {v w : Site 2}
-- given
  (h : dcw_isBarrierEdge ω n v w) :
-- imply
  dualConfig ω (crossEdge s(v, w)) = true := by
-- proof
  apply StatMech.Universality.dcw_barrier_dual_open ω n h

/--
[dcw_barrier_dualAdj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/DualCircuitToWalk.lean)
-/
@[path]
private lemma dcw_barrier_dualAdj_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {v w : Site 2}
-- given
  (h : dcw_isBarrierEdge ω n v w) :
-- imply
  (openSubgraph 2 (dualConfig ω)).Adj (rot90Fun v) (rot90Fun w) := by
-- proof
  apply StatMech.Universality.dcw_barrier_dualAdj ω n h

/--
[dcw_leftSide_in_L](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/DualCircuitToWalk.lean)
-/
@[path]
private lemma dcw_leftSide_in_L_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {x : Site 2}
-- given
  (hx : x ∈ leftSide 0 n 0 n) :
-- imply
  x ∈ bcd_leftReach ω n := by
-- proof
  apply StatMech.Universality.dcw_leftSide_in_L ω n hx

/--
[dcw_rightSide_notin_L](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/DualCircuitToWalk.lean)
-/
@[path]
private lemma dcw_rightSide_notin_L_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {y : Site 2}
-- given
  (hnoH : ¬ HorizontalCrossing ω 0 n 0 n)
  (hy : y ∈ rightSide 0 n 0 n) :
-- imply
  y ∉ bcd_leftReach ω n := by
-- proof
  apply StatMech.Universality.dcw_rightSide_notin_L ω n hnoH hy

/--
[dcw_barrier_separates](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/DualCircuitToWalk.lean)
-/
@[path]
private lemma dcw_barrier_separates_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {x y : Site 2}
-- given
  (hnoH : ¬ HorizontalCrossing ω 0 n 0 n)
  (hx : x ∈ leftSide 0 n 0 n)
  (hy : y ∈ rightSide 0 n 0 n) :
-- imply
  ¬ (latticeMinusBarrier (bcd_leftReach ω n)).Reachable x y := by
-- proof
  apply StatMech.Universality.dcw_barrier_separates ω n hnoH hx hy

/--
[dcw_leftRight_crossCount_odd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/DualCircuitToWalk.lean)
-/
@[path]
private lemma dcw_leftRight_crossCount_odd_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {x y : Site 2}
  {w : (hypercubicLattice 2).Walk x y}
-- given
  (hnoH : ¬ HorizontalCrossing ω 0 n 0 n)
  (hx : x ∈ leftSide 0 n 0 n)
  (hy : y ∈ rightSide 0 n 0 n) :
-- imply
  ¬ Even (crossCount (bcd_leftReach ω n) w) := by
-- proof
  apply StatMech.Universality.dcw_leftRight_crossCount_odd ω n hnoH hx hy w

/--
[dcw_primal_blocks_dual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/DualCircuitToWalk.lean)
-/
@[path]
private lemma dcw_primal_blocks_dual_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {ω : ConfigSpace (Sym2 (Site 2))}
  {x y : Site 2}
  {w : (openSubgraph 2 ω).Walk x y}
  {x' y' : Site 2}
  {w' : (openSubgraph 2 (dualConfig ω)).Walk x' y'}
  {e : Sym2 (Site 2)}
-- given
  (he : e ∈ w.edges)
  (he' : crossEdge e ∈ w'.edges) :
-- imply
  False := by
-- proof
  apply StatMech.Universality.dcw_primal_blocks_dual ω w w' e he he'

/--
[dcw_dualBarrierGraph_le_open](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/DualCircuitToWalk.lean)
-/
@[path]
private lemma dcw_dualBarrierGraph_le_open_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ} :
-- imply
  dcw_dualBarrierGraph ω n ≤ openSubgraph 2 (dualConfig ω) := by
-- proof
  apply StatMech.Universality.dcw_dualBarrierGraph_le_open ω n

/--
[dcw_dualBarrier_reachable_open](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/DualCircuitToWalk.lean)
-/
@[path]
private lemma dcw_dualBarrier_reachable_open_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {p q : Site 2}
-- given
  (h : (dcw_dualBarrierGraph ω n).Reachable p q) :
-- imply
  (openSubgraph 2 (dualConfig ω)).Reachable p q := by
-- proof
  apply StatMech.Universality.dcw_dualBarrier_reachable_open ω n h

/--
[dcw_dualVerticalCrossing_of_route](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/DualCircuitToWalk.lean)
-/
@[path]
private lemma dcw_dualVerticalCrossing_of_route_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
-- given
  (hroute : dcw_BarrierRoute ω n) :
-- imply
  DualVerticalCrossing ω 0 n 0 n := by
-- proof
  apply StatMech.Universality.dcw_dualVerticalCrossing_of_route ω n hroute

/--
[dcw_dualVertical_of_no_horizontal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/DualCircuitToWalk.lean)
-/
@[path]
private lemma dcw_dualVertical_of_no_horizontal_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
-- given
  (hroute : dcw_BarrierRoute ω n) :
-- imply
  DualVerticalCrossing ω 0 n 0 n := by
-- proof
  apply StatMech.Universality.dcw_dualVertical_of_no_horizontal ω n hroute

/--
[dcw_square_dichotomy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/DualCircuitToWalk.lean)
-/
@[path]
private lemma dcw_square_dichotomy_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {n : ℤ}
-- given
  (hroute : ∀ ω : ConfigSpace (Sym2 (Site 2)), ¬ HorizontalCrossing ω 0 n 0 n → dcw_BarrierRoute ω n) :
-- imply
  (horizontalCrossingEvent 0 n 0 n)ᶜ ⊆ dualVerticalCrossingEvent 0 n 0 n := by
-- proof
  apply StatMech.Universality.dcw_square_dichotomy n hroute

/--
[dcw_dualBarrier_isOpenDual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/DualCircuitToWalk.lean)
-/
@[path]
private lemma dcw_dualBarrier_isOpenDual_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {n : ℤ}
-- given
  (hroute : ∀ ω : ConfigSpace (Sym2 (Site 2)), ¬ HorizontalCrossing ω 0 n 0 n → dcw_BarrierRoute ω n) :
-- imply
  (horizontalCrossingEvent 0 n 0 n)ᶜ ⊆ dualVerticalCrossingEvent 0 n 0 n := by
-- proof
  apply StatMech.Universality.dcw_dualBarrier_isOpenDual n hroute

/--
[dcw_barrierEdge_exists](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/DualCircuitToWalk.lean)
-/
@[path]
private lemma dcw_barrierEdge_exists_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
-- given
  (hn : 0 ≤ n)
  (hnoH : ¬ HorizontalCrossing ω 0 n 0 n) :
-- imply
  ∃ v w : Site 2, dcw_isBarrierEdge ω n v w ∧ v 1 = 0 ∧ w 1 = 0 := by
-- proof
  apply StatMech.Universality.dcw_barrierEdge_exists ω n hn hnoH

/--
[dcw_dualBarrierGraph_nonempty_edge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/DualCircuitToWalk.lean)
-/
@[path]
private lemma dcw_dualBarrierGraph_nonempty_edge_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
-- given
  (hn : 0 ≤ n)
  (hnoH : ¬ HorizontalCrossing ω 0 n 0 n) :
-- imply
  ∃ p q : Site 2, (dcw_dualBarrierGraph ω n).Adj p q := by
-- proof
  apply StatMech.Universality.dcw_dualBarrierGraph_nonempty_edge ω n hn hnoH


-- created on 2026-10-23
