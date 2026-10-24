import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.KacWardIntegralAxisWord
open StatMech StatMech.FrontierA


/--
[stepOf_kwHorizontalIntDirection_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardIntegralAxisWord.lean)
-/
@[path]
private lemma stepOf_kwHorizontalIntDirection_nonneg_eq
  {x : ℤ}
-- given
  (hx : 0 ≤ x) :
-- imply
  stepOf (kwHorizontalIntDirection x) = (1, 0) := by
-- proof
  apply StatMech.FrontierA.stepOf_kwHorizontalIntDirection_nonneg hx

/--
[stepOf_kwHorizontalIntDirection_neg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardIntegralAxisWord.lean)
-/
@[path]
private lemma stepOf_kwHorizontalIntDirection_neg_eq
  {x : ℤ}
-- given
  (hx : x < 0) :
-- imply
  stepOf (kwHorizontalIntDirection x) = (-1, 0) := by
-- proof
  apply StatMech.FrontierA.stepOf_kwHorizontalIntDirection_neg hx

/--
[stepOf_kwVerticalIntDirection_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardIntegralAxisWord.lean)
-/
@[path]
private lemma stepOf_kwVerticalIntDirection_nonneg_eq
  {y : ℤ}
-- given
  (hy : 0 ≤ y) :
-- imply
  stepOf (kwVerticalIntDirection y) = (0, 1) := by
-- proof
  apply StatMech.FrontierA.stepOf_kwVerticalIntDirection_nonneg hy

/--
[stepOf_kwVerticalIntDirection_neg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardIntegralAxisWord.lean)
-/
@[path]
private lemma stepOf_kwVerticalIntDirection_neg_eq
  {y : ℤ}
-- given
  (hy : y < 0) :
-- imply
  stepOf (kwVerticalIntDirection y) = (0, -1) := by
-- proof
  apply StatMech.FrontierA.stepOf_kwVerticalIntDirection_neg hy

/--
[sum_replicate_horizontalDirection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardIntegralAxisWord.lean)
-/
@[path]
private lemma sum_replicate_horizontalDirection_eq
  {x : ℤ} :
-- imply
  (List.replicate x.natAbs (stepOf (kwHorizontalIntDirection x))).sum = (x, 0) := by
-- proof
  apply StatMech.FrontierA.sum_replicate_horizontalDirection x

/--
[sum_replicate_verticalDirection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardIntegralAxisWord.lean)
-/
@[path]
private lemma sum_replicate_verticalDirection_eq
  {y : ℤ} :
-- imply
  (List.replicate y.natAbs (stepOf (kwVerticalIntDirection y))).sum = (0, y) := by
-- proof
  apply StatMech.FrontierA.sum_replicate_verticalDirection y

/--
[kwIntegralAxisWord_step_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardIntegralAxisWord.lean)
-/
@[path]
private lemma kwIntegralAxisWord_step_sum_eq
  {v : ℤ × ℤ} :
-- imply
  ((kwIntegralAxisWord v).map stepOf).sum = v := by
-- proof
  apply StatMech.FrontierA.kwIntegralAxisWord_step_sum v

/--
[kwIntegralAxisWord_length](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardIntegralAxisWord.lean)
-/
@[path]
private lemma kwIntegralAxisWord_length_eq
  {v : ℤ × ℤ} :
-- imply
  (kwIntegralAxisWord v).length = v.1.natAbs + v.2.natAbs := by
-- proof
  apply StatMech.FrontierA.kwIntegralAxisWord_length v

/--
[kwIntegralAxisWord_ne_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardIntegralAxisWord.lean)
-/
@[path]
private lemma kwIntegralAxisWord_ne_nil_eq
  {v : ℤ × ℤ}
-- given
  (hv : v ≠ 0) :
-- imply
  kwIntegralAxisWord v ≠ [] := by
-- proof
  apply StatMech.FrontierA.kwIntegralAxisWord_ne_nil hv

/--
[kwIntegralPolygonEdgeWord_step_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardIntegralAxisWord.lean)
-/
@[path]
private lemma kwIntegralPolygonEdgeWord_step_sum_eq
  {n : ℕ}
  [NeZero n]
  {p : Fin n → ℤ × ℤ}
  {i : Fin n} :
-- imply
  ((kwIntegralPolygonEdgeWord p i).map stepOf).sum = p (i + 1) - p i := by
-- proof
  apply StatMech.FrontierA.kwIntegralPolygonEdgeWord_step_sum p i

/--
[kwIntegralPolygonWord_step_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardIntegralAxisWord.lean)
-/
@[path]
private lemma kwIntegralPolygonWord_step_sum_eq
  {n : ℕ}
  [NeZero n]
  {p : Fin n → ℤ × ℤ} :
-- imply
  ((kwIntegralPolygonWord p).map stepOf).sum = 0 := by
-- proof
  apply StatMech.FrontierA.kwIntegralPolygonWord_step_sum p

/--
[kwIntegralPolygonWord_ne_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardIntegralAxisWord.lean)
-/
@[path]
private lemma kwIntegralPolygonWord_ne_nil_eq
  {n : ℕ}
  [NeZero n]
  {p : Fin n → ℤ × ℤ}
-- given
  (hn : 2 ≤ n)
  (hp : Function.Injective p) :
-- imply
  kwIntegralPolygonWord p ≠ [] := by
-- proof
  apply StatMech.FrontierA.kwIntegralPolygonWord_ne_nil p hn hp

/--
[kwIntegralPolygonDirection_closed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardIntegralAxisWord.lean)
-/
@[path]
private lemma kwIntegralPolygonDirection_closed_eq
  {n : ℕ}
  [NeZero n]
  {p : Fin n → ℤ × ℤ} :
-- imply
  ∑ k, stepOf (kwIntegralPolygonDirection p k) = 0 := by
-- proof
  apply StatMech.FrontierA.kwIntegralPolygonDirection_closed p


-- created on 2026-10-23
