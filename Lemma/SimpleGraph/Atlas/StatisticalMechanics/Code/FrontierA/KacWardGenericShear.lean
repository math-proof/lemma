import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardGenericShear.Part2
open StatMech StatMech.FrontierA


/--
[kwShearX_re](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardGenericShear.lean)
-/
@[path]
private lemma kwShearX_re_eq
  {t : ℝ}
  {z : ℂ} :
-- imply
  (kwShearX t z).re = z.re + t * z.im := by
-- proof
  apply StatMech.FrontierA.kwShearX_re t z

/--
[kwShearX_im](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardGenericShear.lean)
-/
@[path]
private lemma kwShearX_im_eq
  {t : ℝ}
  {z : ℂ} :
-- imply
  (kwShearX t z).im = z.im := by
-- proof
  apply StatMech.FrontierA.kwShearX_im t z

/--
[kwShearY_re](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardGenericShear.lean)
-/
@[path]
private lemma kwShearY_re_eq
  {t : ℝ}
  {z : ℂ} :
-- imply
  (kwShearY t z).re = z.re := by
-- proof
  apply StatMech.FrontierA.kwShearY_re t z

/--
[kwShearY_im](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardGenericShear.lean)
-/
@[path]
private lemma kwShearY_im_eq
  {t : ℝ}
  {z : ℂ} :
-- imply
  (kwShearY t z).im = z.im + t * z.re := by
-- proof
  apply StatMech.FrontierA.kwShearY_im t z

/--
[kwComplexCross_shearX](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardGenericShear.lean)
-/
@[path]
private lemma kwComplexCross_shearX_eq
  {t : ℝ}
  {z w : ℂ} :
-- imply
  kwComplexCross (kwShearX t z) (kwShearX t w) = kwComplexCross z w := by
-- proof
  apply StatMech.FrontierA.kwComplexCross_shearX t z w

/--
[kwComplexCross_shearY](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardGenericShear.lean)
-/
@[path]
private lemma kwComplexCross_shearY_eq
  {t : ℝ}
  {z w : ℂ} :
-- imply
  kwComplexCross (kwShearY t z) (kwShearY t w) = kwComplexCross z w := by
-- proof
  apply StatMech.FrontierA.kwComplexCross_shearY t z w

/--
[KWFiniteSimplePolygon.mapLinearEquiv_vertex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardGenericShear.lean)
-/
@[path]
private lemma mapLinearEquiv_vertex_eq
  {n : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
  {e : ℂ ≃ₗ[ℝ] ℂ}
  {i : Fin n} :
-- imply
  (polygon.mapLinearEquiv e).vertex i = e (polygon.vertex i) := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.mapLinearEquiv_vertex polygon e i

/--
[KWFiniteSimplePolygon.mapLinearEquiv_edgeVector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardGenericShear.lean)
-/
@[path]
private lemma mapLinearEquiv_edgeVector_eq
  {n : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
  {e : ℂ ≃ₗ[ℝ] ℂ}
  {i : Fin n} :
-- imply
  (polygon.mapLinearEquiv e).edgeVector i = e (polygon.edgeVector i) := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.mapLinearEquiv_edgeVector polygon e i

/--
[KWFiniteSimplePolygon.exists_shearX_re_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardGenericShear.lean)
-/
@[path]
private lemma exists_shearX_re_ne_zero_eq
  {n : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n} :
-- imply
  ∃ t : ℝ, ∀ i : Fin n, (kwShearX t (polygon.edgeVector i)).re ≠ 0 := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.exists_shearX_re_ne_zero polygon

/--
[KWFiniteSimplePolygon.exists_generic_shear](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardGenericShear.lean)
-/
@[path]
private lemma exists_generic_shear_eq
  {n : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n} :
-- imply
  ∃ tx ty : ℝ, ∀ i : Fin n, (kwShearY ty (kwShearX tx (polygon.edgeVector i))).re ≠ 0 ∧ (kwShearY ty (kwShearX tx (polygon.edgeVector i))).im ≠ 0 := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.exists_generic_shear polygon

/--
[KWFiniteSimplePolygon.exists_generic_coordinate_polygon](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardGenericShear.lean)
-/
@[path]
private lemma exists_generic_coordinate_polygon_eq
  {n : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n} :
-- imply
  ∃ tx ty : ℝ, let e := (kwShearXLinearEquiv tx).trans (kwShearYLinearEquiv ty) ∀ i : Fin n, ((polygon.mapLinearEquiv e).edgeVector i).re ≠ 0 ∧ ((polygon.mapLinearEquiv e).edgeVector i).im ≠ 0 := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.exists_generic_coordinate_polygon polygon


-- created on 2026-10-23
