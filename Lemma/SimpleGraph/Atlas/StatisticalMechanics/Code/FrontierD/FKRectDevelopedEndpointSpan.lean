import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.FKRectDevelopedEndpointSpan
open Set StatMech StatMech.FrontierD


/--
[fkRectDevelopedThreeByOneVertex_column_val](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedEndpointSpan.lean)
-/
@[path]
private lemma fkRectDevelopedThreeByOneVertex_column_val_eq
  {R : FKRectTorus}
  {n : Nat}
  {z : fkRectDevelopedThreeByOneRect n}
-- given
  (hwidth : 4 * n < R.width)
  (hheight : 4 * n < R.height) :
-- imply
  ((fkRectDevelopedSquareVertex R n z.1).1.val : Int) = z.1 1 + n + (z.1 0 - z.1 1 + n) / 2 := by
-- proof
  apply StatMech.FrontierD.fkRectDevelopedThreeByOneVertex_column_val R n hwidth hheight z

/--
[developedEndpoint_physical_span](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedEndpointSpan.lean)
-/
@[path]
private lemma developedEndpoint_physical_span_eq
  {a b : Int}
  {n : Nat} :
-- imply
  (n : Int) ≤ 2 * := by
-- proof
  apply StatMech.FrontierD.developedEndpoint_physical_span a b n

/--
[fkRectDevelopedThreeByOneEndpoint_physical_span](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedEndpointSpan.lean)
-/
@[path]
private lemma fkRectDevelopedThreeByOneEndpoint_physical_span_eq
  {R : FKRectTorus}
  {n : Nat}
  {p : (fkRectDevelopedThreeByOneRect n) × (fkRectDevelopedThreeByOneRect n)}
-- given
  (hwidth : 4 * n < R.width)
  (hheight : 4 * n < R.height)
  (hp : p ∈ fkRectDevelopedThreeByOneVerticalEndpointPairs n) :
-- imply
  let x := fkRectDevelopedSquareVertex R n p.1 let y := fkRectDevelopedSquareVertex R n p.2 (n : Int) ≤ 2 * := by
-- proof
  apply StatMech.FrontierD.fkRectDevelopedThreeByOneEndpoint_physical_span R n hwidth hheight p hp

/--
[fkRectCritical_developedThreeByOne_exists_carrierConnection_span_ge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedEndpointSpan.lean)
-/
@[path]
private lemma fkRectCritical_developedThreeByOne_exists_carrierConnection_span_ge_eq
  {R : FKRectTorus}
  {n : Nat}
  {q : Real}
-- given
  (hn : 1 ≤ n)
  (hwidth : 4 * n < R.width)
  (hheight : 4 * n < R.height)
  (hq : 1 ≤ q) :
-- imply
  ∃ p ∈ fkRectDevelopedThreeByOneVerticalEndpointPairs n, let x := fkRectDevelopedSquareVertex R n p.1 let y := fkRectDevelopedSquareVertex R n p.2 1 / (2 * (1 + q)) / (((3 * n + 1) ^ 2 : Nat) : Real) ≤ fkRectCriticalEventMass R q (fkRectDevelopedThreeByOneCarrierConnectionEvent R n p) ∧ ((n : Int) ≤ 2 * |(y.2.val : Int) - x.2.val| ∨ (n : Int) ≤ 4 * |(y.1.val : Int) - x.1.val|) := by
-- proof
  apply StatMech.FrontierD.fkRectCritical_developedThreeByOne_exists_carrierConnection_span_ge R n hn hwidth hheight hq


-- created on 2026-10-23
