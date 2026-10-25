import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDevelopedHorizontalEndpoint
open Set StatMech StatMech.FrontierD


/--
[mem_fkRectDevelopedThreeByOneHorizontalEndpointPairs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedHorizontalEndpoint.lean)
-/
@[path]
private lemma mem_fkRectDevelopedThreeByOneHorizontalEndpointPairs_eq
  {n : Nat}
  {p : (fkRectDevelopedThreeByOneRect n) × (fkRectDevelopedThreeByOneRect n)} :
-- imply
  p ∈ fkRectDevelopedThreeByOneHorizontalEndpointPairs n ↔ p.1.1 0 = 0 ∧ p.2.1 0 = 3 * (n : Int) := by
-- proof
  apply StatMech.FrontierD.mem_fkRectDevelopedThreeByOneHorizontalEndpointPairs n p

/--
[fkRectDevelopedThreeByOneHorizontalCrossingEvent_eq_endpointUnion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedHorizontalEndpoint.lean)
-/
@[path]
private lemma fkRectDevelopedThreeByOneHorizontalCrossingEvent_eq_endpointUnion_eq
  {R : FKRectTorus}
  {n : Nat} :
-- imply
  fkRectDevelopedRectangleHorizontalCrossingEvent R n 0 (3 * (n : Int)) 0 n = fkRectFiniteEventUnion (fkRectDevelopedThreeByOneHorizontalEndpointPairs n) (fkRectDevelopedThreeByOneEndpointConnectionEvent R n) := by
-- proof
  apply StatMech.FrontierD.fkRectDevelopedThreeByOneHorizontalCrossingEvent_eq_endpointUnion R n

/--
[fkRectDevelopedThreeByOneHorizontalEndpointPairs_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedHorizontalEndpoint.lean)
-/
@[path]
private lemma fkRectDevelopedThreeByOneHorizontalEndpointPairs_nonempty_eq
  {n : Nat} :
-- imply
  (fkRectDevelopedThreeByOneHorizontalEndpointPairs n).Nonempty := by
-- proof
  apply StatMech.FrontierD.fkRectDevelopedThreeByOneHorizontalEndpointPairs_nonempty n

/--
[fkRectDevelopedThreeByOneHorizontalEndpointPairs_card_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedHorizontalEndpoint.lean)
-/
@[path]
private lemma fkRectDevelopedThreeByOneHorizontalEndpointPairs_card_le_eq
  {n : Nat} :
-- imply
  (fkRectDevelopedThreeByOneHorizontalEndpointPairs n).card ≤ (n + 1) ^ 2 := by
-- proof
  apply StatMech.FrontierD.fkRectDevelopedThreeByOneHorizontalEndpointPairs_card_le n

/--
[fkRectCritical_developedThreeByOne_exists_horizontalEndpoint_ge_of_crossingFloor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedHorizontalEndpoint.lean)
-/
@[path]
private lemma fkRectCritical_developedThreeByOne_exists_horizontalEndpoint_ge_of_crossingFloor_eq
  {R : FKRectTorus}
  {n : Nat}
  {q crossingFloor : Real}
-- given
  (hq : 1 ≤ q)
  (hcross : crossingFloor ≤ fkRectCriticalEventMass R q (fkRectDevelopedRectangleHorizontalCrossingEvent R n 0 (3 * (n : Int)) 0 n)) :
-- imply
  ∃ p ∈ fkRectDevelopedThreeByOneHorizontalEndpointPairs n, crossingFloor ≤ ((3 * n + 1) ^ 2 : Nat) * fkRectCriticalEventMass R q (fkRectDevelopedThreeByOneEndpointConnectionEvent R n p) := by
-- proof
  apply StatMech.FrontierD.fkRectCritical_developedThreeByOne_exists_horizontalEndpoint_ge_of_crossingFloor R n hq hcross

/--
[fkRectCritical_developedThreeByOne_exists_horizontalEndpoint_ge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedHorizontalEndpoint.lean)
-/
@[path]
private lemma fkRectCritical_developedThreeByOne_exists_horizontalEndpoint_ge_eq
  {R : FKRectTorus}
  {n : Nat}
  {q : Real}
-- given
  (hq : 1 ≤ q)
  (hcross : 1 / (2 * (1 + q)) ≤ fkRectCriticalEventMass R q (fkRectDevelopedRectangleHorizontalCrossingEvent R n 0 (3 * (n : Int)) 0 n)) :
-- imply
  ∃ p ∈ fkRectDevelopedThreeByOneHorizontalEndpointPairs n, 1 / (2 * (1 + q)) ≤ ((3 * n + 1) ^ 2 : Nat) * fkRectCriticalEventMass R q (fkRectDevelopedThreeByOneEndpointConnectionEvent R n p) := by
-- proof
  apply StatMech.FrontierD.fkRectCritical_developedThreeByOne_exists_horizontalEndpoint_ge R n hq hcross

/--
[fkRectDevelopedThreeByOneHorizontalEndpoint_row_span](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedHorizontalEndpoint.lean)
-/
@[path]
private lemma fkRectDevelopedThreeByOneHorizontalEndpoint_row_span_eq
  {R : FKRectTorus}
  {n : Nat}
  {p : (fkRectDevelopedThreeByOneRect n) × (fkRectDevelopedThreeByOneRect n)}
-- given
  (hwidth : 4 * n < R.width)
  (hheight : 4 * n < R.height)
  (hp : p ∈ fkRectDevelopedThreeByOneHorizontalEndpointPairs n) :
-- imply
  (2 * n : Int) ≤ ((fkRectDevelopedSquareVertex R n p.2).2.val : Int) - (fkRectDevelopedSquareVertex R n p.1).2.val := by
-- proof
  apply StatMech.FrontierD.fkRectDevelopedThreeByOneHorizontalEndpoint_row_span R n hwidth hheight p hp

/--
[fkRectCritical_developedThreeByOne_exists_horizontalReflectedCarrier_ge_of_crossingFloor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedHorizontalEndpoint.lean)
-/
@[path]
private lemma fkRectCritical_developedThreeByOne_exists_horizontalReflectedCarrier_ge_of_crossingFloor_eq
  {R : FKRectTorus}
  {n : Nat}
  {q crossingFloor : Real}
-- given
  (hn : 1 ≤ n)
  (hwidth : 4 * n < R.width)
  (hheight : 4 * n < R.height)
  (hq : 1 ≤ q)
  (hcrossingFloor : 0 < crossingFloor)
  (hcross : crossingFloor ≤ fkRectCriticalEventMass R q (fkRectDevelopedRectangleHorizontalCrossingEvent R n 0 (3 * (n : Int)) 0 n)) :
-- imply
  ∃ p ∈ fkRectDevelopedThreeByOneHorizontalEndpointPairs n, let S := fkRectDevelopedThreeByOneTorusCarrier R n let x : S := fkRectDevelopedThreeByOneCarrierVertex R n p.1 let y : S := fkRectDevelopedThreeByOneCarrierVertex R n p.2 (n : Int) ≤ 2 * := by
-- proof
  apply StatMech.FrontierD.fkRectCritical_developedThreeByOne_exists_horizontalReflectedCarrier_ge_of_crossingFloor R n hn hwidth hheight hq hcrossingFloor hcross

/--
[fkRectCritical_developedThreeByOne_exists_horizontalReflectedCarrier_ge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedHorizontalEndpoint.lean)
-/
@[path]
private lemma fkRectCritical_developedThreeByOne_exists_horizontalReflectedCarrier_ge_eq
  {R : FKRectTorus}
  {n : Nat}
  {q : Real}
-- given
  (hn : 1 ≤ n)
  (hwidth : 4 * n < R.width)
  (hheight : 4 * n < R.height)
  (hq : 1 ≤ q)
  (hcross : 1 / (2 * (1 + q)) ≤ fkRectCriticalEventMass R q (fkRectDevelopedRectangleHorizontalCrossingEvent R n 0 (3 * (n : Int)) 0 n)) :
-- imply
  ∃ p ∈ fkRectDevelopedThreeByOneHorizontalEndpointPairs n, let S := fkRectDevelopedThreeByOneTorusCarrier R n let x : S := fkRectDevelopedThreeByOneCarrierVertex R n p.1 let y : S := fkRectDevelopedThreeByOneCarrierVertex R n p.2 (n : Int) ≤ 2 * := by
-- proof
  apply StatMech.FrontierD.fkRectCritical_developedThreeByOne_exists_horizontalReflectedCarrier_ge R n hn hwidth hheight hq hcross

/--
[fkRectCritical_developedThreeByOne_exists_horizontalPositiveRowBlock_of_crossingFloor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedHorizontalEndpoint.lean)
-/
@[path]
private lemma fkRectCritical_developedThreeByOne_exists_horizontalPositiveRowBlock_of_crossingFloor_eq
  {R : FKRectTorus}
  {n : Nat}
  {q crossingFloor : Real}
-- given
  (hn : 1 ≤ n)
  (hwidth : 12 * n + 2 < R.width)
  (hheight : 12 * n + 2 < R.height)
  (hq : 1 ≤ q)
  (hcrossingFloor : 0 < crossingFloor)
  (hcross : crossingFloor ≤ fkRectCriticalEventMass R q (fkRectDevelopedRectangleHorizontalCrossingEvent R n 0 (3 * (n : Int)) 0 n)) :
-- imply
  ∃ B : FKRectPositiveRowOrientedBlock R q n, B.block.massFloor = fkRectDevelopedReflectedEndpointLowerOf crossingFloor n := by
-- proof
  apply StatMech.FrontierD.fkRectCritical_developedThreeByOne_exists_horizontalPositiveRowBlock_of_crossingFloor R n hn hwidth hheight hq hcrossingFloor hcross

/--
[fkRectCritical_developedThreeByOne_exists_horizontalPositiveRowBlock](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedHorizontalEndpoint.lean)
-/
@[path]
private lemma fkRectCritical_developedThreeByOne_exists_horizontalPositiveRowBlock_eq
  {R : FKRectTorus}
  {n : Nat}
  {q : Real}
-- given
  (hn : 1 ≤ n)
  (hwidth : 12 * n + 2 < R.width)
  (hheight : 12 * n + 2 < R.height)
  (hq : 1 ≤ q)
  (hcross : 1 / (2 * (1 + q)) ≤ fkRectCriticalEventMass R q (fkRectDevelopedRectangleHorizontalCrossingEvent R n 0 (3 * (n : Int)) 0 n)) :
-- imply
  Nonempty (FKRectPositiveRowOrientedBlock R q n) := by
-- proof
  apply StatMech.FrontierD.fkRectCritical_developedThreeByOne_exists_horizontalPositiveRowBlock R n hn hwidth hheight hq hcross

/--
[fkRectCritical_developedThreeByOne_exists_horizontalPositiveBandBlock_of_crossingFloor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedHorizontalEndpoint.lean)
-/
@[path]
private lemma fkRectCritical_developedThreeByOne_exists_horizontalPositiveBandBlock_of_crossingFloor_eq
  {R : FKRectTorus}
  {n : Nat}
  {q crossingFloor : Real}
-- given
  (hn : 1 ≤ n)
  (hwidth : 12 * n + 2 < R.width)
  (hheight : 12 * n + 2 < R.height)
  (hq : 1 ≤ q)
  (hcrossingFloor : 0 < crossingFloor)
  (hcross : crossingFloor ≤ fkRectCriticalEventMass R q (fkRectDevelopedRectangleHorizontalCrossingEvent R n 0 (3 * (n : Int)) 0 n)) :
-- imply
  ∃ B : FKRectPositiveBandOrientedBlock R q n, B.massFloor = fkRectDevelopedReflectedEndpointLowerOf crossingFloor n := by
-- proof
  apply StatMech.FrontierD.fkRectCritical_developedThreeByOne_exists_horizontalPositiveBandBlock_of_crossingFloor R n hn hwidth hheight hq hcrossingFloor hcross

/--
[fkRectCritical_developedThreeByOne_exists_horizontalPositiveBandBlock](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedHorizontalEndpoint.lean)
-/
@[path]
private lemma fkRectCritical_developedThreeByOne_exists_horizontalPositiveBandBlock_eq
  {R : FKRectTorus}
  {n : Nat}
  {q : Real}
-- given
  (hn : 1 ≤ n)
  (hwidth : 12 * n + 2 < R.width)
  (hheight : 12 * n + 2 < R.height)
  (hq : 1 ≤ q)
  (hcross : 1 / (2 * (1 + q)) ≤ fkRectCriticalEventMass R q (fkRectDevelopedRectangleHorizontalCrossingEvent R n 0 (3 * (n : Int)) 0 n)) :
-- imply
  Nonempty (FKRectPositiveBandOrientedBlock R q n) := by
-- proof
  apply StatMech.FrontierD.fkRectCritical_developedThreeByOne_exists_horizontalPositiveBandBlock R n hn hwidth hheight hq hcross


-- created on 2026-10-23
