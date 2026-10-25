import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusSiteReflection.Part10
open Finset StatMech StatMech.FrontierA


/--
[isingTorusSiteReflect_apply_same](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusSiteReflection.lean)
-/
@[path]
private lemma isingTorusSiteReflect_apply_same_eq
  {d k : Nat}
  {i : Fin d}
  {x : IsingDyadicTorus d k} :
-- imply
  isingTorusSiteReflect i x i = -x i := by
-- proof
  apply StatMech.FrontierA.isingTorusSiteReflect_apply_same i x

/--
[isingTorusSiteReflect_apply_of_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusSiteReflection.lean)
-/
@[path]
private lemma isingTorusSiteReflect_apply_of_ne_eq
  {d k : Nat}
  {i j : Fin d}
  {x : IsingDyadicTorus d k}
-- given
  (hji : j ≠ i) :
-- imply
  isingTorusSiteReflect i x j = x j := by
-- proof
  apply StatMech.FrontierA.isingTorusSiteReflect_apply_of_ne i j hji x

/--
[isingTorusSiteReflect_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusSiteReflection.lean)
-/
@[path]
private lemma isingTorusSiteReflect_involutive_eq
  {d k : Nat}
  {i : Fin d}
  {x : IsingDyadicTorus d k} :
-- imply
  isingTorusSiteReflect i (isingTorusSiteReflect i x) = x := by
-- proof
  apply StatMech.FrontierA.isingTorusSiteReflect_involutive i x

/--
[isingTorusSiteReflect_fixed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusSiteReflection.lean)
-/
@[path]
private lemma isingTorusSiteReflect_fixed_eq
  {d k : Nat}
  {i : Fin d}
  {x : IsingDyadicTorus d k}
-- given
  (hx : isingTorusOnSitePlane i x) :
-- imply
  isingTorusSiteReflect i x = x := by
-- proof
  apply StatMech.FrontierA.isingTorusSiteReflect_fixed i hx

/--
[isingTorusSiteReflect_strictLower_of_upper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusSiteReflection.lean)
-/
@[path]
private lemma isingTorusSiteReflect_strictLower_of_upper_eq
  {d k : Nat}
  {i : Fin d}
  {x : IsingDyadicTorus d k}
-- given
  (hplane : ¬ isingTorusOnSitePlane i x)
  (hlower : ¬ isingTorusInStrictLower i x) :
-- imply
  isingTorusInStrictLower i (isingTorusSiteReflect i x) := by
-- proof
  apply StatMech.FrontierA.isingTorusSiteReflect_strictLower_of_upper i hplane hlower

/--
[isingTorusSiteReflect_not_plane](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusSiteReflection.lean)
-/
@[path]
private lemma isingTorusSiteReflect_not_plane_eq
  {d k : Nat}
  {i : Fin d}
  {x : IsingDyadicTorus d k}
-- given
  (hx : ¬ isingTorusOnSitePlane i x) :
-- imply
  ¬ isingTorusOnSitePlane i (isingTorusSiteReflect i x) := by
-- proof
  apply StatMech.FrontierA.isingTorusSiteReflect_not_plane i hx

/--
[isingTorusSiteSplit_glue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusSiteReflection.lean)
-/
@[path]
private lemma isingTorusSiteSplit_glue_eq
  {d k : Nat}
  {i : Fin d}
-- given
  (boundary : ConfigSpace (IsingTorusSitePlane (k := k) i))
  (lower upper : ConfigSpace (IsingTorusStrictLower (k := k) i)) :
-- imply
  isingTorusSiteSplit i (isingTorusSiteGlue i boundary lower upper) = (boundary, (lower, upper)) := by
-- proof
  apply StatMech.FrontierA.isingTorusSiteSplit_glue i boundary lower upper

/--
[isingTorusSiteGlue_split](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusSiteReflection.lean)
-/
@[path]
private lemma isingTorusSiteGlue_split_eq
  {d k : Nat}
  {i : Fin d}
  {sigma : ConfigSpace (IsingDyadicTorus d k)} :
-- imply
  isingTorusSiteGlue i (isingTorusSiteSplit i sigma).1 (isingTorusSiteSplit i sigma).2.1 (isingTorusSiteSplit i sigma).2.2 = sigma := by
-- proof
  apply StatMech.FrontierA.isingTorusSiteGlue_split i sigma

/--
[isingTorusSiteReflect_add_step_same](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusSiteReflection.lean)
-/
@[path]
private lemma isingTorusSiteReflect_add_step_same_eq
  {d k : Nat}
  {i : Fin d}
  {x : IsingDyadicTorus d k} :
-- imply
  isingTorusSiteReflect i (x + isingTorusStep i) = isingTorusSiteReflect i x - isingTorusStep i := by
-- proof
  apply StatMech.FrontierA.isingTorusSiteReflect_add_step_same i x

/--
[isingTorusSiteReflect_add_step_of_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusSiteReflection.lean)
-/
@[path]
private lemma isingTorusSiteReflect_add_step_of_ne_eq
  {d k : Nat}
  {i j : Fin d}
  {x : IsingDyadicTorus d k}
-- given
  (hji : j ≠ i) :
-- imply
  isingTorusSiteReflect i (x + isingTorusStep j) = isingTorusSiteReflect i x + isingTorusStep j := by
-- proof
  apply StatMech.FrontierA.isingTorusSiteReflect_add_step_of_ne i j hji x

/--
[isingTorusDirichlet_siteReflectField](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusSiteReflection.lean)
-/
@[path]
private lemma isingTorusDirichlet_siteReflectField_eq
  {d k : Nat}
  {i : Fin d}
  {u : IsingDyadicTorus d k → Real} :
-- imply
  isingTorusDirichlet (isingTorusSiteReflectField i u) = isingTorusDirichlet u := by
-- proof
  apply StatMech.FrontierA.isingTorusDirichlet_siteReflectField i u

/--
[isingTorusDirichletBilinear_siteReflectField](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusSiteReflection.lean)
-/
@[path]
private lemma isingTorusDirichletBilinear_siteReflectField_eq
  {d k : Nat}
  {i : Fin d}
  {u v : IsingDyadicTorus d k → Real} :
-- imply
  isingTorusDirichletBilinear (isingTorusSiteReflectField i u) (isingTorusSiteReflectField i v) = isingTorusDirichletBilinear u v := by
-- proof
  apply StatMech.FrontierA.isingTorusDirichletBilinear_siteReflectField i u v

/--
[isingTorusSiteReflect_strictLower_iff_upper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusSiteReflection.lean)
-/
@[path]
private lemma isingTorusSiteReflect_strictLower_iff_upper_eq
  {d k : Nat}
  {i : Fin d}
  {x : IsingDyadicTorus d k} :
-- imply
  isingTorusInStrictLower i (isingTorusSiteReflect i x) ↔ 2 ^ (k + 1) < (x i).val := by
-- proof
  apply StatMech.FrontierA.isingTorusSiteReflect_strictLower_iff_upper i x

/--
[isingTorusStrictLowerField_reflect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusSiteReflection.lean)
-/
@[path]
private lemma isingTorusStrictLowerField_reflect_eq
  {d k : Nat}
  {i : Fin d}
-- given
  (lower : ConfigSpace (IsingTorusStrictLower (k := k) i)) :
-- imply
  isingTorusSiteReflectField i (isingTorusStrictLowerField i lower) = isingTorusStrictUpperField i lower := by
-- proof
  apply StatMech.FrontierA.isingTorusStrictLowerField_reflect i lower

/--
[isingTorusSitePlaneField_reflect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusSiteReflection.lean)
-/
@[path]
private lemma isingTorusSitePlaneField_reflect_eq
  {d k : Nat}
  {i : Fin d}
-- given
  (boundary : ConfigSpace (IsingTorusSitePlane (k := k) i)) :
-- imply
  isingTorusSiteReflectField i (isingTorusSitePlaneField i boundary) = isingTorusSitePlaneField i boundary := by
-- proof
  apply StatMech.FrontierA.isingTorusSitePlaneField_reflect i boundary

/--
[isingTorusStrictLower_upper_cross_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusSiteReflection.lean)
-/
@[path]
private lemma isingTorusStrictLower_upper_cross_zero_eq
  {d k : Nat}
  {i : Fin d}
-- given
  (lower upper : ConfigSpace (IsingTorusStrictLower (k := k) i)) :
-- imply
  isingTorusDirichletBilinear (isingTorusStrictLowerField i lower) (isingTorusStrictUpperField i upper) = 0 := by
-- proof
  apply StatMech.FrontierA.isingTorusStrictLower_upper_cross_zero i lower upper

/--
[isingTorusSpinSiteGlue_eq_fields](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusSiteReflection.lean)
-/
@[path]
private lemma isingTorusSpinSiteGlue_eq_fields_eq
  {d k : Nat}
  {i : Fin d}
-- given
  (boundary : ConfigSpace (IsingTorusSitePlane (k := k) i))
  (lower upper : ConfigSpace (IsingTorusStrictLower (k := k) i)) :
-- imply
  isingTorusSpinField (isingTorusSiteGlue i boundary lower upper) = isingTorusSitePlaneField i boundary + isingTorusStrictLowerField i lower + isingTorusStrictUpperField i upper := by
-- proof
  apply StatMech.FrontierA.isingTorusSpinSiteGlue_eq_fields i boundary lower upper

/--
[isingTorusStrictUpper_dirichlet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusSiteReflection.lean)
-/
@[path]
private lemma isingTorusStrictUpper_dirichlet_eq
  {d k : Nat}
  {i : Fin d}
-- given
  (lower : ConfigSpace (IsingTorusStrictLower (k := k) i)) :
-- imply
  isingTorusDirichlet (isingTorusStrictUpperField i lower) = isingTorusDirichlet (isingTorusStrictLowerField i lower) := by
-- proof
  apply StatMech.FrontierA.isingTorusStrictUpper_dirichlet i lower

/--
[isingTorusSitePlane_upper_bilinear](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusSiteReflection.lean)
-/
@[path]
private lemma isingTorusSitePlane_upper_bilinear_eq
  {d k : Nat}
  {i : Fin d}
-- given
  (boundary : ConfigSpace (IsingTorusSitePlane (k := k) i))
  (lower : ConfigSpace (IsingTorusStrictLower (k := k) i)) :
-- imply
  isingTorusDirichletBilinear (isingTorusSitePlaneField i boundary) (isingTorusStrictUpperField i lower) = isingTorusDirichletBilinear (isingTorusSitePlaneField i boundary) (isingTorusStrictLowerField i lower) := by
-- proof
  apply StatMech.FrontierA.isingTorusSitePlane_upper_bilinear i boundary lower

/--
[isingTorusSiteGlue_dirichlet_midpoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusSiteReflection.lean)
-/
@[path]
private lemma isingTorusSiteGlue_dirichlet_midpoint_eq
  {d k : Nat}
  {i : Fin d}
-- given
  (boundary : ConfigSpace (IsingTorusSitePlane (k := k) i))
  (lower upper : ConfigSpace (IsingTorusStrictLower (k := k) i)) :
-- imply
  2 * isingTorusDirichlet (isingTorusSpinField (isingTorusSiteGlue i boundary lower upper)) = isingTorusDirichlet (isingTorusSpinField (isingTorusSiteGlue i boundary lower lower)) + isingTorusDirichlet (isingTorusSpinField (isingTorusSiteGlue i boundary upper upper)) := by
-- proof
  apply StatMech.FrontierA.isingTorusSiteGlue_dirichlet_midpoint i boundary lower upper

/--
[isingTorusSiteWeight_factor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusSiteReflection.lean)
-/
@[path]
private lemma isingTorusSiteWeight_factor_eq
  {d k : Nat}
  {i : Fin d}
  {beta : Real}
-- given
  (boundary : ConfigSpace (IsingTorusSitePlane (k := k) i))
  (lower upper : ConfigSpace (IsingTorusStrictLower (k := k) i)) :
-- imply
  Real.exp (-(beta / 2) * isingTorusDirichlet (isingTorusSpinField (isingTorusSiteGlue i boundary lower upper))) = isingTorusSiteHalfWeight i beta boundary lower * isingTorusSiteHalfWeight i beta boundary upper := by
-- proof
  apply StatMech.FrontierA.isingTorusSiteWeight_factor i beta boundary lower upper

/--
[isingTorusSiteReflectionForm_eq_amplitudes](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusSiteReflection.lean)
-/
@[path]
private lemma isingTorusSiteReflectionForm_eq_amplitudes_eq
  {d k : Nat}
  {i : Fin d}
  {beta : Real}
-- given
  (F G : ConfigSpace (IsingTorusStrictLower (k := k) i) → Real) :
-- imply
  isingTorusSiteReflectionForm i beta F G = ∑ boundary : ConfigSpace (IsingTorusSitePlane (k := k) i), isingTorusSiteBoundaryAmplitude i beta boundary F * isingTorusSiteBoundaryAmplitude i beta boundary G := by
-- proof
  apply StatMech.FrontierA.isingTorusSiteReflectionForm_eq_amplitudes i beta F G

/--
[isingTorusSiteReflectionForm_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusSiteReflection.lean)
-/
@[path]
private lemma isingTorusSiteReflectionForm_nonneg_eq
  {d k : Nat}
  {i : Fin d}
  {beta : Real}
-- given
  (F : ConfigSpace (IsingTorusStrictLower (k := k) i) → Real) :
-- imply
  0 ≤ isingTorusSiteReflectionForm i beta F F := by
-- proof
  apply StatMech.FrontierA.isingTorusSiteReflectionForm_nonneg i beta F

/--
[isingTorusSiteReflectionForm_cauchy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusSiteReflection.lean)
-/
@[path]
private lemma isingTorusSiteReflectionForm_cauchy_eq
  {d k : Nat}
  {i : Fin d}
  {beta : Real}
-- given
  (F G : ConfigSpace (IsingTorusStrictLower (k := k) i) → Real) :
-- imply
  isingTorusSiteReflectionForm i beta F G ^ 2 ≤ isingTorusSiteReflectionForm i beta F F * isingTorusSiteReflectionForm i beta G G := by
-- proof
  apply StatMech.FrontierA.isingTorusSiteReflectionForm_cauchy i beta F G

/--
[isingTorusSiteReflectionForm_spin_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusSiteReflection.lean)
-/
@[path]
private lemma isingTorusSiteReflectionForm_spin_eq_eq
  {d k : Nat}
  {i : Fin d}
  {beta : Real}
-- given
  (x y : IsingTorusStrictLower (k := k) i) :
-- imply
  isingTorusSiteReflectionForm i beta (isingTorusStrictHalfSpin x) (isingTorusStrictHalfSpin y) = ∑ sigma : ConfigSpace (IsingDyadicTorus d k), Real.exp (-(beta / 2) * isingTorusDirichlet (isingTorusSpinField sigma)) * isingTorusSpinField sigma x.1 * isingTorusSpinField sigma (isingTorusSiteReflect i y.1) := by
-- proof
  apply StatMech.FrontierA.isingTorusSiteReflectionForm_spin_eq i beta x y

/--
[isingTorusTwoPoint_siteReflection_cauchy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusSiteReflection.lean)
-/
@[path]
private lemma isingTorusTwoPoint_siteReflection_cauchy_eq
  {d k : Nat}
  {i : Fin d}
  {beta : Real}
-- given
  (x y : IsingTorusStrictLower (k := k) i) :
-- imply
  isingTorusTwoPoint beta x.1 (isingTorusSiteReflect i y.1) ^ 2 ≤ isingTorusTwoPoint beta x.1 (isingTorusSiteReflect i x.1) * isingTorusTwoPoint beta y.1 (isingTorusSiteReflect i y.1) := by
-- proof
  apply StatMech.FrontierA.isingTorusTwoPoint_siteReflection_cauchy i beta x y

/--
[isingTorusSiteReflect_coordinateShift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusSiteReflection.lean)
-/
@[path]
private lemma isingTorusSiteReflect_coordinateShift_eq
  {d k : Nat}
  {i : Fin d}
  {n : Nat} :
-- imply
  isingTorusSiteReflect i (isingTorusCoordinateShift (k := k) i n) = -isingTorusCoordinateShift i n := by
-- proof
  apply StatMech.FrontierA.isingTorusSiteReflect_coordinateShift i n

/--
[isingTorusTwoPoint_axis_site_midpoint_sq_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusSiteReflection.lean)
-/
@[path]
private lemma isingTorusTwoPoint_axis_site_midpoint_sq_le_eq
  {d k : Nat}
  {i : Fin d}
  {beta : Real}
  {a b : Nat}
-- given
  (ha0 : 0 < a)
  (hb0 : 0 < b)
  (ha : a < 2 ^ (k + 1))
  (hb : b < 2 ^ (k + 1)) :
-- imply
  isingTorusTwoPoint (k := k) beta 0 (isingTorusCoordinateShift i (a + b)) ^ 2 ≤ isingTorusTwoPoint (k := k) beta 0 (isingTorusCoordinateShift i (2 * a)) * isingTorusTwoPoint (k := k) beta 0 (isingTorusCoordinateShift i (2 * b)) := by
-- proof
  apply StatMech.FrontierA.isingTorusTwoPoint_axis_site_midpoint_sq_le i beta a b ha0 hb0 ha hb


-- created on 2026-10-23
