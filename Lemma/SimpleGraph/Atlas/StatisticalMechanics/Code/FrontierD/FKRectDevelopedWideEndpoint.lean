import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDevelopedWideEndpoint.Part4
open Set StatMech StatMech.FrontierD


/--
[mem_fkRectDevelopedThreeByOneVerticalEndpointPairs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedWideEndpoint.lean)
-/
@[path]
private lemma mem_fkRectDevelopedThreeByOneVerticalEndpointPairs_eq
  {n : Nat}
  {p : (fkRectDevelopedThreeByOneRect n) × (fkRectDevelopedThreeByOneRect n)} :
-- imply
  p ∈ fkRectDevelopedThreeByOneVerticalEndpointPairs n ↔ p.1.1 1 = 0 ∧ p.2.1 1 = n := by
-- proof
  apply StatMech.FrontierD.mem_fkRectDevelopedThreeByOneVerticalEndpointPairs n p

/--
[fkRectDevelopedThreeByOne_undevelop_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedWideEndpoint.lean)
-/
@[path]
private lemma fkRectDevelopedThreeByOne_undevelop_bounds_eq
  {R : FKRectTorus}
  {n : Nat}
  {z : Site 2}
-- given
  (hwidth : 4 * n < R.width)
  (hheight : 4 * n < R.height)
  (hz : z ∈ fkRectDevelopedThreeByOneRect n) :
-- imply
  let p := fkRectSquareUndevelopPoint (fkRectDevelopedSquarePoint n z) 0 ≤ p.1 ∧ p.1 < R.width ∧ 0 ≤ p.2 ∧ p.2 < R.height := by
-- proof
  apply StatMech.FrontierD.fkRectDevelopedThreeByOne_undevelop_bounds R n hwidth hheight hz

/--
[fkRectVertexSquarePoint_developedThreeByOneVertex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedWideEndpoint.lean)
-/
@[path]
private lemma fkRectVertexSquarePoint_developedThreeByOneVertex_eq
  {R : FKRectTorus}
  {n : Nat}
  {z : Site 2}
-- given
  (hwidth : 4 * n < R.width)
  (hheight : 4 * n < R.height)
  (hz : z ∈ fkRectDevelopedThreeByOneRect n) :
-- imply
  fkRectVertexSquarePoint R (fkRectDevelopedSquareVertex R n z) = fkRectDevelopedSquarePoint n z := by
-- proof
  apply StatMech.FrontierD.fkRectVertexSquarePoint_developedThreeByOneVertex R n hwidth hheight hz

/--
[fkRectVertexSquareSite_developedThreeByOneVertex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedWideEndpoint.lean)
-/
@[path]
private lemma fkRectVertexSquareSite_developedThreeByOneVertex_eq
  {R : FKRectTorus}
  {n : Nat}
  {z : Site 2}
-- given
  (hwidth : 4 * n < R.width)
  (hheight : 4 * n < R.height)
  (hz : z ∈ fkRectDevelopedThreeByOneRect n) :
-- imply
  fkRectVertexSquareSite R (fkRectDevelopedSquareVertex R n z) = fkRectDevelopedSquareSite n z := by
-- proof
  apply StatMech.FrontierD.fkRectVertexSquareSite_developedThreeByOneVertex R n hwidth hheight hz

/--
[fkRectDevelopedThreeByOneVertex_cutGraph_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedWideEndpoint.lean)
-/
@[path]
private lemma fkRectDevelopedThreeByOneVertex_cutGraph_adj_eq
  {R : FKRectTorus}
  {n : Nat}
  {z w : Site 2}
-- given
  (hwidth : 4 * n < R.width)
  (hheight : 4 * n < R.height)
  (hz : z ∈ fkRectDevelopedThreeByOneRect n)
  (hw : w ∈ fkRectDevelopedThreeByOneRect n)
  (hzw : (hypercubicLattice 2).Adj z w) :
-- imply
  (fkRectCutGraph R).Adj (fkRectDevelopedSquareVertex R n z) (fkRectDevelopedSquareVertex R n w) := by
-- proof
  apply StatMech.FrontierD.fkRectDevelopedThreeByOneVertex_cutGraph_adj R n hwidth hheight hz hw hzw

/--
[fkRectDevelopedThreeByOnePullback_open_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedWideEndpoint.lean)
-/
@[path]
private lemma fkRectDevelopedThreeByOnePullback_open_iff_eq
  {R : FKRectTorus}
  {n : Nat}
  {omega : R.Configuration}
  {z w : Site 2}
-- given
  (hwidth : 4 * n < R.width)
  (hheight : 4 * n < R.height)
  (hz : z ∈ fkRectDevelopedThreeByOneRect n)
  (hw : w ∈ fkRectDevelopedThreeByOneRect n)
  (hzw : (hypercubicLattice 2).Adj z w) :
-- imply
  fkRectDevelopedSquarePullback R n omega s(z, w) = true ↔ (fkRectOpenGraph R omega).Adj (fkRectDevelopedSquareVertex R n z) (fkRectDevelopedSquareVertex R n w) := by
-- proof
  apply StatMech.FrontierD.fkRectDevelopedThreeByOnePullback_open_iff R n hwidth hheight omega hz hw hzw

/--
[fkRectDevelopedThreeByOneEndpointConnection_imp_torusReachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedWideEndpoint.lean)
-/
@[path]
private lemma fkRectDevelopedThreeByOneEndpointConnection_imp_torusReachable_eq
  {R : FKRectTorus}
  {n : Nat}
  {omega : R.Configuration}
  {p : (fkRectDevelopedThreeByOneRect n) × (fkRectDevelopedThreeByOneRect n)}
-- given
  (hwidth : 4 * n < R.width)
  (hheight : 4 * n < R.height)
  (hconn : omega ∈ fkRectDevelopedThreeByOneEndpointConnectionEvent R n p) :
-- imply
  (fkRectOpenGraph R omega).Reachable (fkRectDevelopedSquareVertex R n p.1) (fkRectDevelopedSquareVertex R n p.2) := by
-- proof
  apply StatMech.FrontierD.fkRectDevelopedThreeByOneEndpointConnection_imp_torusReachable R n hwidth hheight omega p hconn

/--
[fkRectDevelopedThreeByOneTorusEndpointConnectionEvent_isIncreasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedWideEndpoint.lean)
-/
@[path]
private lemma fkRectDevelopedThreeByOneTorusEndpointConnectionEvent_isIncreasing_eq
  {R : FKRectTorus}
  {n : Nat}
  {p : (fkRectDevelopedThreeByOneRect n) × (fkRectDevelopedThreeByOneRect n)} :
-- imply
  IsIncreasing (fkRectDevelopedThreeByOneTorusEndpointConnectionEvent R n p) := by
-- proof
  apply StatMech.FrontierD.fkRectDevelopedThreeByOneTorusEndpointConnectionEvent_isIncreasing R n p

/--
[fkRectDevelopedThreeByOneEndpointConnection_subset_torus](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedWideEndpoint.lean)
-/
@[path]
private lemma fkRectDevelopedThreeByOneEndpointConnection_subset_torus_eq
  {R : FKRectTorus}
  {n : Nat}
  {p : (fkRectDevelopedThreeByOneRect n) × (fkRectDevelopedThreeByOneRect n)}
-- given
  (hwidth : 4 * n < R.width)
  (hheight : 4 * n < R.height) :
-- imply
  fkRectDevelopedThreeByOneEndpointConnectionEvent R n p ⊆ fkRectDevelopedThreeByOneTorusEndpointConnectionEvent R n p := by
-- proof
  apply StatMech.FrontierD.fkRectDevelopedThreeByOneEndpointConnection_subset_torus R n hwidth hheight p

/--
[fkRectDevelopedThreeByOneEndpointConnectionEvent_isIncreasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedWideEndpoint.lean)
-/
@[path]
private lemma fkRectDevelopedThreeByOneEndpointConnectionEvent_isIncreasing_eq
  {R : FKRectTorus}
  {n : Nat}
  {p : (fkRectDevelopedThreeByOneRect n) × (fkRectDevelopedThreeByOneRect n)} :
-- imply
  IsIncreasing (fkRectDevelopedThreeByOneEndpointConnectionEvent R n p) := by
-- proof
  apply StatMech.FrontierD.fkRectDevelopedThreeByOneEndpointConnectionEvent_isIncreasing R n p

/--
[fkRectDevelopedThreeByOneVerticalCrossingEvent_eq_endpointUnion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedWideEndpoint.lean)
-/
@[path]
private lemma fkRectDevelopedThreeByOneVerticalCrossingEvent_eq_endpointUnion_eq
  {R : FKRectTorus}
  {n : Nat} :
-- imply
  fkRectDevelopedRectangleVerticalCrossingEvent R n 0 (3 * (n : Int)) 0 n = fkRectFiniteEventUnion (fkRectDevelopedThreeByOneVerticalEndpointPairs n) (fkRectDevelopedThreeByOneEndpointConnectionEvent R n) := by
-- proof
  apply StatMech.FrontierD.fkRectDevelopedThreeByOneVerticalCrossingEvent_eq_endpointUnion R n

/--
[fkRectDevelopedThreeByOneVerticalEndpointPairs_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedWideEndpoint.lean)
-/
@[path]
private lemma fkRectDevelopedThreeByOneVerticalEndpointPairs_nonempty_eq
  {n : Nat} :
-- imply
  (fkRectDevelopedThreeByOneVerticalEndpointPairs n).Nonempty := by
-- proof
  apply StatMech.FrontierD.fkRectDevelopedThreeByOneVerticalEndpointPairs_nonempty n

/--
[fkRectDevelopedThreeByOneVerticalEndpointPairs_card_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedWideEndpoint.lean)
-/
@[path]
private lemma fkRectDevelopedThreeByOneVerticalEndpointPairs_card_le_eq
  {n : Nat} :
-- imply
  (fkRectDevelopedThreeByOneVerticalEndpointPairs n).card ≤ (3 * n + 1) ^ 2 := by
-- proof
  apply StatMech.FrontierD.fkRectDevelopedThreeByOneVerticalEndpointPairs_card_le n

/--
[fkRectCritical_developedThreeByOne_exists_endpoint_ge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedWideEndpoint.lean)
-/
@[path]
private lemma fkRectCritical_developedThreeByOne_exists_endpoint_ge_eq
  {R : FKRectTorus}
  {n : Nat}
  {q : Real}
-- given
  (hn : 1 <= n)
  (hwidth : 3 * n < R.width)
  (hheight : 3 * n < R.height)
  (hq : 1 <= q) :
-- imply
  ∃ p ∈ fkRectDevelopedThreeByOneVerticalEndpointPairs n, 1 / (2 * (1 + q)) ≤ ((3 * n + 1) ^ 2 : Nat) * fkRectCriticalEventMass R q (fkRectDevelopedThreeByOneEndpointConnectionEvent R n p) := by
-- proof
  apply StatMech.FrontierD.fkRectCritical_developedThreeByOne_exists_endpoint_ge R n hn hwidth hheight hq

/--
[fkRectCritical_developedThreeByOne_exists_torus_endpoint_ge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedWideEndpoint.lean)
-/
@[path]
private lemma fkRectCritical_developedThreeByOne_exists_torus_endpoint_ge_eq
  {R : FKRectTorus}
  {n : Nat}
  {q : Real}
-- given
  (hn : 1 <= n)
  (hwidth : 4 * n < R.width)
  (hheight : 4 * n < R.height)
  (hq : 1 <= q) :
-- imply
  ∃ p ∈ fkRectDevelopedThreeByOneVerticalEndpointPairs n, 1 / (2 * (1 + q)) ≤ ((3 * n + 1) ^ 2 : Nat) * fkRectCriticalEventMass R q (fkRectDevelopedThreeByOneTorusEndpointConnectionEvent R n p) := by
-- proof
  apply StatMech.FrontierD.fkRectCritical_developedThreeByOne_exists_torus_endpoint_ge R n hn hwidth hheight hq


-- created on 2026-10-23
