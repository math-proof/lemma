import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardExtremeVertex
open StatMech StatMech.FrontierA


/--
[two_mul_kwComplexDot_sub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardExtremeVertex.lean)
-/
@[path]
private lemma two_mul_kwComplexDot_sub_eq
  {x y : ℂ} :
-- imply
  2 * kwComplexDot x (y - x) = Complex.normSq y - Complex.normSq x - Complex.normSq (y - x) := by
-- proof
  apply StatMech.FrontierA.two_mul_kwComplexDot_sub x y

/--
[normSq_mul_kwComplexCross_eq_supportDet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardExtremeVertex.lean)
-/
@[path]
private lemma normSq_mul_kwComplexCross_eq_supportDet_eq
  {u v w : ℂ} :
-- imply
  Complex.normSq u * kwComplexCross v w = kwComplexCross u v * (-kwComplexDot u w) - kwComplexCross u w * (-kwComplexDot u v) := by
-- proof
  apply StatMech.FrontierA.normSq_mul_kwComplexCross_eq_supportDet u v w

/--
[kwComplexDot_mul_real_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardExtremeVertex.lean)
-/
@[path]
private lemma kwComplexDot_mul_real_right_eq
  {r : ℝ}
  {u v : ℂ} :
-- imply
  kwComplexDot u ((r : ℂ) * v) = r * kwComplexDot u v := by
-- proof
  apply StatMech.FrontierA.kwComplexDot_mul_real_right r u v

/--
[normSq_mul_real](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardExtremeVertex.lean)
-/
@[path]
private lemma normSq_mul_real_eq
  {r : ℝ}
  {v : ℂ} :
-- imply
  Complex.normSq ((r : ℂ) * v) = r ^ 2 * Complex.normSq v := by
-- proof
  apply StatMech.FrontierA.normSq_mul_real r v

/--
[KWFiniteSimplePolygon.exists_strictSupportingVertex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardExtremeVertex.lean)
-/
@[path]
private lemma exists_strictSupportingVertex_eq
  {n : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n} :
-- imply
  ∃ i : Fin n, ∀ j : Fin n, j ≠ i → kwComplexDot (polygon.vertex i) (polygon.vertex j - polygon.vertex i) < 0 := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.exists_strictSupportingVertex polygon

/--
[KWFiniteSimplePolygon.exists_upperTangentVertex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardExtremeVertex.lean)
-/
@[path]
private lemma exists_upperTangentVertex_eq
  {n : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
-- given
  (hsupport : ∀ j : Fin n, j ≠ i → kwComplexDot (polygon.vertex i) (polygon.vertex j - polygon.vertex i) < 0) :
-- imply
  ∃ j : Fin n, j ≠ i ∧ ∀ k : Fin n, 0 ≤ kwComplexCross (polygon.vertex j - polygon.vertex i) (polygon.vertex k - polygon.vertex i) := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.exists_upperTangentVertex polygon i hsupport

/--
[KWFiniteSimplePolygon.exists_nearestUpperTangentVertex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardExtremeVertex.lean)
-/
@[path]
private lemma exists_nearestUpperTangentVertex_eq
  {n : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
-- given
  (hsupport : ∀ j : Fin n, j ≠ i → kwComplexDot (polygon.vertex i) (polygon.vertex j - polygon.vertex i) < 0) :
-- imply
  ∃ j : Fin n, j ≠ i ∧ (∀ k : Fin n, 0 ≤ kwComplexCross (polygon.vertex j - polygon.vertex i) (polygon.vertex k - polygon.vertex i)) ∧ ∀ k : Fin n, k ≠ i → k ≠ j → ¬Sbtw ℝ (polygon.vertex i) (polygon.vertex k) (polygon.vertex j) := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.exists_nearestUpperTangentVertex polygon i hsupport

/--
[KWFiniteSimplePolygon.exists_lowerTangentVertex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardExtremeVertex.lean)
-/
@[path]
private lemma exists_lowerTangentVertex_eq
  {n : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
-- given
  (hsupport : ∀ j : Fin n, j ≠ i → kwComplexDot (polygon.vertex i) (polygon.vertex j - polygon.vertex i) < 0) :
-- imply
  ∃ j : Fin n, j ≠ i ∧ ∀ k : Fin n, kwComplexCross (polygon.vertex j - polygon.vertex i) (polygon.vertex k - polygon.vertex i) ≤ 0 := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.exists_lowerTangentVertex polygon i hsupport

/--
[KWFiniteSimplePolygon.exists_nearestLowerTangentVertex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardExtremeVertex.lean)
-/
@[path]
private lemma exists_nearestLowerTangentVertex_eq
  {n : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
-- given
  (hsupport : ∀ j : Fin n, j ≠ i → kwComplexDot (polygon.vertex i) (polygon.vertex j - polygon.vertex i) < 0) :
-- imply
  ∃ j : Fin n, j ≠ i ∧ (∀ k : Fin n, kwComplexCross (polygon.vertex j - polygon.vertex i) (polygon.vertex k - polygon.vertex i) ≤ 0) ∧ ∀ k : Fin n, k ≠ i → k ≠ j → ¬Sbtw ℝ (polygon.vertex i) (polygon.vertex k) (polygon.vertex j) := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.exists_nearestLowerTangentVertex polygon i hsupport

/--
[KWFiniteSimplePolygon.exists_distinctNearestTangentVertices](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardExtremeVertex.lean)
-/
@[path]
private lemma exists_distinctNearestTangentVertices_eq
  {n : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
-- given
  (hnoncollinear : ∀ i : Fin n, ¬Collinear ℝ ({polygon.vertex i, polygon.vertex (i + 1), polygon.vertex (i + 2)} : Set ℂ))
  (hsupport : ∀ j : Fin n, j ≠ i → kwComplexDot (polygon.vertex i) (polygon.vertex j - polygon.vertex i) < 0) :
-- imply
  ∃ lower upper : Fin n, lower ≠ i ∧ upper ≠ i ∧ lower ≠ upper ∧ (∀ k : Fin n, kwComplexCross (polygon.vertex lower - polygon.vertex i) (polygon.vertex k - polygon.vertex i) ≤ 0) ∧ (∀ k : Fin n, 0 ≤ kwComplexCross (polygon.vertex upper - polygon.vertex i) (polygon.vertex k - polygon.vertex i)) ∧ (∀ k : Fin n, k ≠ i → k ≠ lower → ¬Sbtw ℝ (polygon.vertex i) (polygon.vertex k) (polygon.vertex lower)) ∧ (∀ k : Fin n, k ≠ i → k ≠ upper → ¬Sbtw ℝ (polygon.vertex i) (polygon.vertex k) (polygon.vertex upper)) := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.exists_distinctNearestTangentVertices polygon hnoncollinear i hsupport

/--
[KWFiniteSimplePolygon.exists_distinctTangentVertices](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardExtremeVertex.lean)
-/
@[path]
private lemma exists_distinctTangentVertices_eq
  {n : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
-- given
  (hnoncollinear : ∀ i : Fin n, ¬Collinear ℝ ({polygon.vertex i, polygon.vertex (i + 1), polygon.vertex (i + 2)} : Set ℂ))
  (hsupport : ∀ j : Fin n, j ≠ i → kwComplexDot (polygon.vertex i) (polygon.vertex j - polygon.vertex i) < 0) :
-- imply
  ∃ lower upper : Fin n, lower ≠ i ∧ upper ≠ i ∧ lower ≠ upper ∧ (∀ k : Fin n, kwComplexCross (polygon.vertex lower - polygon.vertex i) (polygon.vertex k - polygon.vertex i) ≤ 0) ∧ (∀ k : Fin n, 0 ≤ kwComplexCross (polygon.vertex upper - polygon.vertex i) (polygon.vertex k - polygon.vertex i)) := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.exists_distinctTangentVertices polygon hnoncollinear i hsupport


-- created on 2026-10-23
