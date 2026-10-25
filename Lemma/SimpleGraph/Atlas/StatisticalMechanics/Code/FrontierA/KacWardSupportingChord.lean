import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardSupportingChord.Part4
open StatMech StatMech.FrontierA


/--
[kw_eq_real_mul_of_cross_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardSupportingChord.lean)
-/
@[path]
private lemma kw_eq_real_mul_of_cross_eq_zero_eq
  {v w : ℂ}
-- given
  (hv : v ≠ 0)
  (hcross : kwComplexCross v w = 0) :
-- imply
  w = ((kwComplexDot v w / Complex.normSq v : ℝ) : ℂ) * v := by
-- proof
  apply StatMech.FrontierA.kw_eq_real_mul_of_cross_eq_zero hv hcross

/--
[kw_lineMap_openSegments_overlap_endpoints_of_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardSupportingChord.lean)
-/
@[path]
private lemma kw_lineMap_openSegments_overlap_endpoints_of_lt_eq
  {A D z : ℂ}
  {x y : ℝ}
-- given
  (hAD : A ≠ D)
  (hxy : x < y)
  (hzAD : Sbtw ℝ A z D)
  (hzXY : Sbtw ℝ (AffineMap.lineMap A D x) z (AffineMap.lineMap A D y)) :
-- imply
  Sbtw ℝ A (AffineMap.lineMap A D x) D ∨ Sbtw ℝ A (AffineMap.lineMap A D y) D ∨ Sbtw ℝ (AffineMap.lineMap A D x) A (AffineMap.lineMap A D y) ∨ Sbtw ℝ (AffineMap.lineMap A D x) D (AffineMap.lineMap A D y) ∨ (AffineMap.lineMap A D x = A ∧ AffineMap.lineMap A D y = D) := by
-- proof
  apply StatMech.FrontierA.kw_lineMap_openSegments_overlap_endpoints_of_lt hAD hxy hzAD hzXY

/--
[kw_lineMap_openSegments_overlap_endpoints](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardSupportingChord.lean)
-/
@[path]
private lemma kw_lineMap_openSegments_overlap_endpoints_eq
  {A D z : ℂ}
  {x y : ℝ}
-- given
  (hAD : A ≠ D)
  (hxy : x ≠ y)
  (hzAD : Sbtw ℝ A z D)
  (hzXY : Sbtw ℝ (AffineMap.lineMap A D x) z (AffineMap.lineMap A D y)) :
-- imply
  Sbtw ℝ A (AffineMap.lineMap A D x) D ∨ Sbtw ℝ A (AffineMap.lineMap A D y) D ∨ Sbtw ℝ (AffineMap.lineMap A D x) A (AffineMap.lineMap A D y) ∨ Sbtw ℝ (AffineMap.lineMap A D x) D (AffineMap.lineMap A D y) ∨ (AffineMap.lineMap A D x = A ∧ AffineMap.lineMap A D y = D) ∨ (AffineMap.lineMap A D x = D ∧ AffineMap.lineMap A D y = A) := by
-- proof
  apply StatMech.FrontierA.kw_lineMap_openSegments_overlap_endpoints hAD hxy hzAD hzXY

/--
[kw_openSegments_overlap_collinear_endpoints](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardSupportingChord.lean)
-/
@[path]
private lemma kw_openSegments_overlap_collinear_endpoints_eq
  {A D X Y z : ℂ}
-- given
  (hAD : A ≠ D)
  (hXY : X ≠ Y)
  (hX : kwComplexCross (D - A) (X - A) = 0)
  (hY : kwComplexCross (D - A) (Y - A) = 0)
  (hzAD : Sbtw ℝ A z D)
  (hzXY : Sbtw ℝ X z Y) :
-- imply
  Sbtw ℝ A X D ∨ Sbtw ℝ A Y D ∨ Sbtw ℝ X A Y ∨ Sbtw ℝ X D Y ∨ (X = A ∧ Y = D) ∨ (X = D ∧ Y = A) := by
-- proof
  apply StatMech.FrontierA.kw_openSegments_overlap_collinear_endpoints hAD hXY hX hY hzAD hzXY

/--
[kw_cross_endpoints_eq_zero_of_intersect_of_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardSupportingChord.lean)
-/
@[path]
private lemma kw_cross_endpoints_eq_zero_of_intersect_of_nonneg_eq
  {A D X Y z : ℂ}
-- given
  (hzAD : Sbtw ℝ A z D)
  (hzXY : Sbtw ℝ X z Y)
  (hX : 0 ≤ kwComplexCross (D - A) (X - A))
  (hY : 0 ≤ kwComplexCross (D - A) (Y - A)) :
-- imply
  kwComplexCross (D - A) (X - A) = 0 ∧ kwComplexCross (D - A) (Y - A) = 0 := by
-- proof
  apply StatMech.FrontierA.kw_cross_endpoints_eq_zero_of_intersect_of_nonneg hzAD hzXY hX hY

/--
[KWFiniteSimplePolygon.chordIsClean_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardSupportingChord.lean)
-/
@[path]
private lemma chordIsClean_symm_eq
  {n : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
  {i j : Fin n}
-- given
  (hclean : polygon.ChordIsClean i j) :
-- imply
  polygon.ChordIsClean j i := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.chordIsClean_symm polygon hclean

/--
[KWFiniteSimplePolygon.chordIsClean_of_supporting](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardSupportingChord.lean)
-/
@[path]
private lemma chordIsClean_of_supporting_eq
  {n : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
  {i j : Fin n}
-- given
  (hij : i ≠ j)
  (hforward : j ≠ i + 1)
  (hbackward : i ≠ j + 1)
  (hside : ∀ k : Fin n, 0 ≤ kwComplexCross (polygon.vertex j - polygon.vertex i) (polygon.vertex k - polygon.vertex i))
  (hvertex : ∀ k : Fin n, k ≠ i → k ≠ j → ¬Sbtw ℝ (polygon.vertex i) (polygon.vertex k) (polygon.vertex j)) :
-- imply
  polygon.ChordIsClean i j := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.chordIsClean_of_supporting polygon i j hij hforward hbackward hside hvertex

/--
[KWFiniteSimplePolygon.exists_nearestUpperTangent_chord](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardSupportingChord.lean)
-/
@[path]
private lemma exists_nearestUpperTangent_chord_eq
  {n : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
-- given
  (hsupport : ∀ j : Fin n, j ≠ i → kwComplexDot (polygon.vertex i) (polygon.vertex j - polygon.vertex i) < 0) :
-- imply
  ∃ j : Fin n, j ≠ i ∧ (j = i + 1 ∨ i = j + 1 ∨ polygon.ChordIsClean i j) := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.exists_nearestUpperTangent_chord polygon i hsupport

/--
[KWFiniteSimplePolygon.exists_exposed_visibleChord_or_neighbor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardSupportingChord.lean)
-/
@[path]
private lemma exists_exposed_visibleChord_or_neighbor_eq
  {n : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n} :
-- imply
  ∃ i j : Fin n, i ≠ j ∧ (j = i + 1 ∨ i = j + 1 ∨ polygon.ChordIsClean i j) := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.exists_exposed_visibleChord_or_neighbor polygon

/--
[KWFiniteSimplePolygon.exists_exposed_visibleChord_or_twoNeighbors](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardSupportingChord.lean)
-/
@[path]
private lemma exists_exposed_visibleChord_or_twoNeighbors_eq
  {n : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
-- given
  (hnoncollinear : ∀ i : Fin n, ¬Collinear ℝ ({polygon.vertex i, polygon.vertex (i + 1), polygon.vertex (i + 2)} : Set ℂ)) :
-- imply
  ∃ i : Fin n, (∃ j : Fin n, j ≠ i ∧ j ≠ i + 1 ∧ i ≠ j + 1 ∧ polygon.ChordIsClean i j) ∨ (∃ lower upper : Fin n, lower ≠ upper ∧ (lower = i + 1 ∨ i = lower + 1) ∧ (upper = i + 1 ∨ i = upper + 1)) := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.exists_exposed_visibleChord_or_twoNeighbors polygon hnoncollinear

/--
[KWFiniteSimplePolygon.vertexOneDiagonalIsClean_of_strictlyOneSided](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardSupportingChord.lean)
-/
@[path]
private lemma vertexOneDiagonalIsClean_of_strictlyOneSided_eq
  {m : ℕ}
  {polygon : KWFiniteSimplePolygon (m + 3)}
-- given
  (hm : 1 ≤ m)
  (hside : polygon.VertexZeroTwoStrictlyOneSided) :
-- imply
  polygon.VertexOneDiagonalIsClean := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.vertexOneDiagonalIsClean_of_strictlyOneSided hm polygon hside

/--
[KWFiniteSimplePolygon.vertexOneDiagonalIsClean_of_strictlySeparated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardSupportingChord.lean)
-/
@[path]
private lemma vertexOneDiagonalIsClean_of_strictlySeparated_eq
  {m : ℕ}
  {polygon : KWFiniteSimplePolygon (m + 3)}
-- given
  (hm : 1 ≤ m)
  (hsep : polygon.VertexOneStrictlySeparated) :
-- imply
  polygon.VertexOneDiagonalIsClean := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.vertexOneDiagonalIsClean_of_strictlySeparated hm polygon hsep

/--
[KWFiniteSimplePolygon.vertexOneAlignedSideEar_of_strictlySeparated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardSupportingChord.lean)
-/
@[path]
private lemma vertexOneAlignedSideEar_of_strictlySeparated_eq
  {m : ℕ}
  {polygon : KWFiniteSimplePolygon (m + 3)}
-- given
  (hm : 1 ≤ m)
  (hsep : polygon.VertexOneStrictlySeparated) :
-- imply
  polygon.VertexOneAlignedSideEar := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.vertexOneAlignedSideEar_of_strictlySeparated hm polygon hsep


-- created on 2026-10-23
