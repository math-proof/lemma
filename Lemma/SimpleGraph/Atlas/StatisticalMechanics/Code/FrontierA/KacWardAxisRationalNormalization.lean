import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.KacWardAxisRationalNormalization
open StatMech StatMech.FrontierA


/--
[kwRatApprox_spec](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAxisRationalNormalization.lean)
-/
@[path]
private lemma kwRatApprox_spec_eq
  {eps : ℝ}
  {x : ℝ}
-- given
  (heps : 0 < eps) :
-- imply
  x - eps < (kwRatApprox eps heps x : ℝ) ∧ (kwRatApprox eps heps x : ℝ) < x + eps := by
-- proof
  apply StatMech.FrontierA.kwRatApprox_spec eps heps x

/--
[abs_kwRatApprox_sub_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAxisRationalNormalization.lean)
-/
@[path]
private lemma abs_kwRatApprox_sub_lt_eq
  {eps : ℝ}
  {x : ℝ}
-- given
  (heps : 0 < eps) :
-- imply
  |(kwRatApprox eps heps x : ℝ) - x| < eps := by
-- proof
  apply StatMech.FrontierA.abs_kwRatApprox_sub_lt eps heps x

/--
[kwAxisRatVertex_re_close](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAxisRationalNormalization.lean)
-/
@[path]
private lemma kwAxisRatVertex_re_close_eq
  {n : ℕ}
  {vertex : Fin n → ℂ}
  {eps : ℝ}
  {i : Fin n}
-- given
  (heps : 0 < eps) :
-- imply
  |(kwRatVertex (kwAxisRatData vertex eps heps) i).re - (vertex i).re| < eps := by
-- proof
  apply StatMech.FrontierA.kwAxisRatVertex_re_close vertex eps heps i

/--
[kwAxisRatVertex_im_close](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAxisRationalNormalization.lean)
-/
@[path]
private lemma kwAxisRatVertex_im_close_eq
  {n : ℕ}
  {vertex : Fin n → ℂ}
  {eps : ℝ}
  {i : Fin n}
-- given
  (heps : 0 < eps) :
-- imply
  |(kwRatVertex (kwAxisRatData vertex eps heps) i).im - (vertex i).im| < eps := by
-- proof
  apply StatMech.FrontierA.kwAxisRatVertex_im_close vertex eps heps i

/--
[dist_kwAxisRatVertex_lt_two_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAxisRationalNormalization.lean)
-/
@[path]
private lemma dist_kwAxisRatVertex_lt_two_mul_eq
  {n : ℕ}
  {vertex : Fin n → ℂ}
  {eps : ℝ}
  {i : Fin n}
-- given
  (heps : 0 < eps) :
-- imply
  dist (kwRatVertex (kwAxisRatData vertex eps heps) i) (vertex i) < 2 * eps := by
-- proof
  apply StatMech.FrontierA.dist_kwAxisRatVertex_lt_two_mul vertex eps heps i

/--
[kwAxisRatVertex_preserves_re_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAxisRationalNormalization.lean)
-/
@[path]
private lemma kwAxisRatVertex_preserves_re_eq_eq
  {n : ℕ}
  {vertex : Fin n → ℂ}
  {eps : ℝ}
  {i j : Fin n}
-- given
  (heps : 0 < eps)
  (h : (vertex i).re = (vertex j).re) :
-- imply
  (kwRatVertex (kwAxisRatData vertex eps heps) i).re = (kwRatVertex (kwAxisRatData vertex eps heps) j).re := by
-- proof
  apply StatMech.FrontierA.kwAxisRatVertex_preserves_re_eq vertex eps heps h

/--
[kwAxisRatVertex_preserves_im_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAxisRationalNormalization.lean)
-/
@[path]
private lemma kwAxisRatVertex_preserves_im_eq_eq
  {n : ℕ}
  {vertex : Fin n → ℂ}
  {eps : ℝ}
  {i j : Fin n}
-- given
  (heps : 0 < eps)
  (h : (vertex i).im = (vertex j).im) :
-- imply
  (kwRatVertex (kwAxisRatData vertex eps heps) i).im = (kwRatVertex (kwAxisRatData vertex eps heps) j).im := by
-- proof
  apply StatMech.FrontierA.kwAxisRatVertex_preserves_im_eq vertex eps heps h

/--
[KWRawTurnAdmissible.of_pos_edge_scales](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAxisRationalNormalization.lean)
-/
@[path]
private lemma of_pos_edge_scales_eq
  {n : ℕ}
  [NeZero n]
  {source target : Fin n → ℂ}
  {scale : Fin n → ℝ}
-- given
  (hsource : ∀ i, KWRawTurnAdmissible source i)
  (hscale : ∀ i, 0 < scale i)
  (hedge : ∀ i, kwRawEdge target i = scale i * kwRawEdge source i) :
-- imply
  ∀ i, KWRawTurnAdmissible target i := by
-- proof
  apply StatMech.FrontierA.KWRawTurnAdmissible.of_pos_edge_scales hsource scale hscale hedge

/--
[KWFiniteSimplePolygon.exists_rational_axis_phaseModel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAxisRationalNormalization.lean)
-/
@[path]
private lemma exists_rational_axis_phaseModel_eq
  {n : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
-- given
  (haxis : ∀ i, (polygon.edgeVector i).re = 0 ∨ (polygon.edgeVector i).im = 0)
  (hturn : ∀ i, KWRawTurnAdmissible polygon.vertex i) :
-- imply
  ∃ (q : Fin n → ℚ × ℚ) (rational : KWFiniteSimplePolygon n), rational.vertex = kwRatVertex q ∧ KWRawNonbacktrackingSimpleData rational.vertex ∧ (∀ i, KWRawTurnAdmissible rational.vertex i) ∧ (∀ i, (rational.edgeVector i).re = 0 ∨ (rational.edgeVector i).im = 0) ∧ kwVectorPhaseCycle polygon.edgeList = kwVectorPhaseCycle rational.edgeList := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.exists_rational_axis_phaseModel polygon haxis hturn

/--
[kwIntComplex_sub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAxisRationalNormalization.lean)
-/
@[path]
private lemma kwIntComplex_sub_eq
  {a b : ℤ × ℤ} :
-- imply
  kwIntComplex (a - b) = kwIntComplex a - kwIntComplex b := by
-- proof
  apply StatMech.FrontierA.kwIntComplex_sub a b

/--
[KWFiniteSimplePolygon.axis_phaseCycle_eq_neg_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAxisRationalNormalization.lean)
-/
@[path]
private lemma axis_phaseCycle_eq_neg_one_eq
  {n : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
-- given
  (haxis : ∀ i, (polygon.edgeVector i).re = 0 ∨ (polygon.edgeVector i).im = 0)
  (hturn : ∀ i, KWRawTurnAdmissible polygon.vertex i) :
-- imply
  kwVectorPhaseCycle polygon.edgeList = -1 := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.axis_phaseCycle_eq_neg_one polygon haxis hturn


-- created on 2026-10-23
