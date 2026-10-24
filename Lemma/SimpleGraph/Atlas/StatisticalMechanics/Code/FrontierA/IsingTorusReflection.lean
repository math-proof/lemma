import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.IsingTorusReflection
open Finset StatMech StatMech.FrontierA


/--
[isingTorusReflectCoord_val](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusReflection.lean)
-/
@[path]
private lemma isingTorusReflectCoord_val_eq
  {d k : Nat}
  {z : ZMod (2 ^ (k + 2))} :
-- imply
  (isingTorusReflectCoord z).val = 2 ^ (k + 2) - 1 - z.val := by
-- proof
  apply StatMech.FrontierA.isingTorusReflectCoord_val z

/--
[isingTorusReflectCoord_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusReflection.lean)
-/
@[path]
private lemma isingTorusReflectCoord_involutive_eq
  {d k : Nat}
  {z : ZMod (2 ^ (k + 2))} :
-- imply
  isingTorusReflectCoord (isingTorusReflectCoord z) = z := by
-- proof
  apply StatMech.FrontierA.isingTorusReflectCoord_involutive z

/--
[isingTorusReflectCoord_eq_neg_sub_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusReflection.lean)
-/
@[path]
private lemma isingTorusReflectCoord_eq_neg_sub_one_eq
  {d k : Nat}
  {z : ZMod (2 ^ (k + 2))} :
-- imply
  isingTorusReflectCoord z = -z - 1 := by
-- proof
  apply StatMech.FrontierA.isingTorusReflectCoord_eq_neg_sub_one z

/--
[isingTorusReflectCoord_add_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusReflection.lean)
-/
@[path]
private lemma isingTorusReflectCoord_add_one_eq
  {d k : Nat}
  {z : ZMod (2 ^ (k + 2))} :
-- imply
  isingTorusReflectCoord (z + 1) = isingTorusReflectCoord z - 1 := by
-- proof
  apply StatMech.FrontierA.isingTorusReflectCoord_add_one z

/--
[isingTorusReflectCoord_sub_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusReflection.lean)
-/
@[path]
private lemma isingTorusReflectCoord_sub_one_eq
  {d k : Nat}
  {z : ZMod (2 ^ (k + 2))} :
-- imply
  isingTorusReflectCoord (z - 1) = isingTorusReflectCoord z + 1 := by
-- proof
  apply StatMech.FrontierA.isingTorusReflectCoord_sub_one z

/--
[isingTorusReflectSite_apply_same](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusReflection.lean)
-/
@[path]
private lemma isingTorusReflectSite_apply_same_eq
  {d k : Nat}
  {i : Fin d}
  {x : IsingDyadicTorus d k} :
-- imply
  isingTorusReflectSite i x i = isingTorusReflectCoord (x i) := by
-- proof
  apply StatMech.FrontierA.isingTorusReflectSite_apply_same i x

/--
[isingTorusReflectSite_apply_of_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusReflection.lean)
-/
@[path]
private lemma isingTorusReflectSite_apply_of_ne_eq
  {d k : Nat}
  {i j : Fin d}
  {x : IsingDyadicTorus d k}
-- given
  (hji : j ≠ i) :
-- imply
  isingTorusReflectSite i x j = x j := by
-- proof
  apply StatMech.FrontierA.isingTorusReflectSite_apply_of_ne i j hji x

/--
[isingTorusStep_apply_same](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusReflection.lean)
-/
@[path]
private lemma isingTorusStep_apply_same_eq
  {d k : Nat}
  {i : Fin d} :
-- imply
  isingTorusStep (k := k) i i = 1 := by
-- proof
  apply StatMech.FrontierA.isingTorusStep_apply_same i

/--
[isingTorusStep_apply_of_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusReflection.lean)
-/
@[path]
private lemma isingTorusStep_apply_of_ne_eq
  {d k : Nat}
  {i j : Fin d}
-- given
  (hji : j ≠ i) :
-- imply
  isingTorusStep (k := k) i j = 0 := by
-- proof
  apply StatMech.FrontierA.isingTorusStep_apply_of_ne i j hji

/--
[isingTorusReflectSite_add_step_same](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusReflection.lean)
-/
@[path]
private lemma isingTorusReflectSite_add_step_same_eq
  {d k : Nat}
  {i : Fin d}
  {x : IsingDyadicTorus d k} :
-- imply
  isingTorusReflectSite i (x + isingTorusStep i) = isingTorusReflectSite i x - isingTorusStep i := by
-- proof
  apply StatMech.FrontierA.isingTorusReflectSite_add_step_same i x

/--
[isingTorusReflectSite_add_step_of_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusReflection.lean)
-/
@[path]
private lemma isingTorusReflectSite_add_step_of_ne_eq
  {d k : Nat}
  {i j : Fin d}
  {x : IsingDyadicTorus d k}
-- given
  (hji : j ≠ i) :
-- imply
  isingTorusReflectSite i (x + isingTorusStep j) = isingTorusReflectSite i x + isingTorusStep j := by
-- proof
  apply StatMech.FrontierA.isingTorusReflectSite_add_step_of_ne i j hji x

/--
[isingTorusReflectCoord_add_one_eq_of_lower_cross](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusReflection.lean)
-/
@[path]
private lemma isingTorusReflectCoord_add_one_eq_of_lower_cross_eq
  {d k : Nat}
  {z : ZMod (2 ^ (k + 2))}
-- given
  (hz : z.val < 2 ^ (k + 1))
  (hcross : ¬(z + 1).val < 2 ^ (k + 1)) :
-- imply
  isingTorusReflectCoord (z + 1) = z := by
-- proof
  apply StatMech.FrontierA.isingTorusReflectCoord_add_one_eq_of_lower_cross z hz hcross

/--
[isingTorusReflectCoord_eq_add_one_of_upper_cross](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusReflection.lean)
-/
@[path]
private lemma isingTorusReflectCoord_eq_add_one_of_upper_cross_eq
  {d k : Nat}
  {z : ZMod (2 ^ (k + 2))}
-- given
  (hz : ¬z.val < 2 ^ (k + 1))
  (hcross : (z + 1).val < 2 ^ (k + 1)) :
-- imply
  isingTorusReflectCoord z = z + 1 := by
-- proof
  apply StatMech.FrontierA.isingTorusReflectCoord_eq_add_one_of_upper_cross z hz hcross

/--
[isingTorus_crossing_reflects_endpoints](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusReflection.lean)
-/
@[path]
private lemma isingTorus_crossing_reflects_endpoints_eq
  {d k : Nat}
  {i j : Fin d}
  {x : IsingDyadicTorus d k} :
-- imply
  (isingTorusInLowerHalf i x ∧ ¬ isingTorusInLowerHalf i (x + isingTorusStep j) → isingTorusReflectSite i (x + isingTorusStep j) = x) ∧ (¬ isingTorusInLowerHalf i x ∧ isingTorusInLowerHalf i (x + isingTorusStep j) → isingTorusReflectSite i x = x + isingTorusStep j) := by
-- proof
  apply StatMech.FrontierA.isingTorus_crossing_reflects_endpoints i j x

/--
[isingTorusReflectSite_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusReflection.lean)
-/
@[path]
private lemma isingTorusReflectSite_involutive_eq
  {d k : Nat}
  {i : Fin d}
  {x : IsingDyadicTorus d k} :
-- imply
  isingTorusReflectSite i (isingTorusReflectSite i x) = x := by
-- proof
  apply StatMech.FrontierA.isingTorusReflectSite_involutive i x

/--
[isingTorusReflectSite_not_lower_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusReflection.lean)
-/
@[path]
private lemma isingTorusReflectSite_not_lower_iff_eq
  {d k : Nat}
  {i : Fin d}
  {x : IsingDyadicTorus d k} :
-- imply
  isingTorusInLowerHalf i (isingTorusReflectSite i x) ↔ ¬ isingTorusInLowerHalf i x := by
-- proof
  apply StatMech.FrontierA.isingTorusReflectSite_not_lower_iff i x

/--
[isingTorusPolarizeLower_reflection_invariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusReflection.lean)
-/
@[path]
private lemma isingTorusPolarizeLower_reflection_invariant_eq
  {d k : Nat}
  {i : Fin d}
  {x : IsingDyadicTorus d k}
-- given
  (h : IsingDyadicTorus d k → Real) :
-- imply
  isingTorusPolarizeLower i h (isingTorusReflectSite i x) = isingTorusPolarizeLower i h x := by
-- proof
  apply StatMech.FrontierA.isingTorusPolarizeLower_reflection_invariant i h x

/--
[isingTorusPolarizeUpper_reflection_invariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusReflection.lean)
-/
@[path]
private lemma isingTorusPolarizeUpper_reflection_invariant_eq
  {d k : Nat}
  {i : Fin d}
  {x : IsingDyadicTorus d k}
-- given
  (h : IsingDyadicTorus d k → Real) :
-- imply
  isingTorusPolarizeUpper i h (isingTorusReflectSite i x) = isingTorusPolarizeUpper i h x := by
-- proof
  apply StatMech.FrontierA.isingTorusPolarizeUpper_reflection_invariant i h x

/--
[isingTorusSplitHalves_glueHalves](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusReflection.lean)
-/
@[path]
private lemma isingTorusSplitHalves_glueHalves_eq
  {d k : Nat}
  {i : Fin d}
-- given
  (lower upper : ConfigSpace (IsingTorusLowerSite (k := k) i)) :
-- imply
  isingTorusSplitHalves i (isingTorusGlueHalves i lower upper) = (lower, upper) := by
-- proof
  apply StatMech.FrontierA.isingTorusSplitHalves_glueHalves i lower upper

/--
[isingTorusGlueHalves_splitHalves](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusReflection.lean)
-/
@[path]
private lemma isingTorusGlueHalves_splitHalves_eq
  {d k : Nat}
  {i : Fin d}
  {sigma : ConfigSpace (IsingDyadicTorus d k)} :
-- imply
  isingTorusGlueHalves i (isingTorusSplitHalves i sigma).1 (isingTorusSplitHalves i sigma).2 = sigma := by
-- proof
  apply StatMech.FrontierA.isingTorusGlueHalves_splitHalves i sigma

/--
[isingTorusSpinGlue_add_field_eq_embeds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusReflection.lean)
-/
@[path]
private lemma isingTorusSpinGlue_add_field_eq_embeds_eq
  {d k : Nat}
  {i : Fin d}
-- given
  (h : IsingDyadicTorus d k → Real)
  (lower upper : ConfigSpace (IsingTorusLowerSite (k := k) i)) :
-- imply
  isingTorusSpinField (isingTorusGlueHalves i lower upper) + h = isingTorusEmbedLower i (isingTorusLowerValues i h lower) + isingTorusEmbedUpper i (isingTorusUpperValues i h upper) := by
-- proof
  apply StatMech.FrontierA.isingTorusSpinGlue_add_field_eq_embeds i h lower upper

/--
[isingTorus_lowerFeature_mul_upperFeature_eq_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusReflection.lean)
-/
@[path]
private lemma isingTorus_lowerFeature_mul_upperFeature_eq_boundary_eq
  {d k : Nat}
  {i : Fin d}
  {e : IsingTorusDirectedEdge d k}
-- given
  (u v : IsingTorusLowerSite (k := k) i → Real) :
-- imply
  isingTorusLowerGradientFeature i u e * isingTorusUpperGradientFeature i v e = isingTorusBoundaryFeature i u e * isingTorusBoundaryFeature i v e := by
-- proof
  apply StatMech.FrontierA.isingTorus_lowerFeature_mul_upperFeature_eq_boundary i u v e

/--
[isingTorus_crossBilinear_eq_neg_boundaryFeatureDot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusReflection.lean)
-/
@[path]
private lemma isingTorus_crossBilinear_eq_neg_boundaryFeatureDot_eq
  {d k : Nat}
  {i : Fin d}
-- given
  (u v : IsingTorusLowerSite (k := k) i → Real) :
-- imply
  isingTorusDirichletBilinear (isingTorusEmbedLower i u) (isingTorusEmbedUpper i v) = -(∑ e : IsingTorusDirectedEdge d k, isingTorusBoundaryFeature i u e * isingTorusBoundaryFeature i v e) := by
-- proof
  apply StatMech.FrontierA.isingTorus_crossBilinear_eq_neg_boundaryFeatureDot i u v

/--
[isingTorus_crossBilinear_eq_neg_featureDot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusReflection.lean)
-/
@[path]
private lemma isingTorus_crossBilinear_eq_neg_featureDot_eq
  {d k : Nat}
  {i : Fin d}
-- given
  (u v : IsingTorusLowerSite (k := k) i → Real) :
-- imply
  isingTorusDirichletBilinear (isingTorusEmbedLower i u) (isingTorusEmbedUpper i v) = -(∑ e : IsingTorusDirectedEdge d k, isingTorusLowerGradientFeature i u e * isingTorusUpperGradientFeature i v e) := by
-- proof
  apply StatMech.FrontierA.isingTorus_crossBilinear_eq_neg_featureDot i u v

/--
[isingTorus_shiftedWeight_factor_halves](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusReflection.lean)
-/
@[path]
private lemma isingTorus_shiftedWeight_factor_halves_eq
  {d k : Nat}
  {i : Fin d}
  {beta : Real}
-- given
  (u v : IsingTorusLowerSite (k := k) i → Real) :
-- imply
  Real.exp (-(beta / 2) * isingTorusDirichlet (isingTorusEmbedLower i u + isingTorusEmbedUpper i v)) = isingTorusLowerHalfWeight i beta u * isingTorusUpperHalfWeight i beta v * Real.exp (beta * ∑ e : IsingTorusDirectedEdge d k, isingTorusLowerGradientFeature i u e * isingTorusUpperGradientFeature i v e) := by
-- proof
  apply StatMech.FrontierA.isingTorus_shiftedWeight_factor_halves i beta u v

/--
[isingTorus_shiftedWeight_factor_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusReflection.lean)
-/
@[path]
private lemma isingTorus_shiftedWeight_factor_boundary_eq
  {d k : Nat}
  {i : Fin d}
  {beta : Real}
-- given
  (u v : IsingTorusLowerSite (k := k) i → Real) :
-- imply
  Real.exp (-(beta / 2) * isingTorusDirichlet (isingTorusEmbedLower i u + isingTorusEmbedUpper i v)) = isingTorusLowerHalfWeight i beta u * isingTorusUpperHalfWeight i beta v * Real.exp (beta * ∑ e : IsingTorusDirectedEdge d k, isingTorusBoundaryFeature i u e * isingTorusBoundaryFeature i v e) := by
-- proof
  apply StatMech.FrontierA.isingTorus_shiftedWeight_factor_boundary i beta u v

/--
[isingTorusDirichlet_reflectField](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusReflection.lean)
-/
@[path]
private lemma isingTorusDirichlet_reflectField_eq
  {d k : Nat}
  {i : Fin d}
  {u : IsingDyadicTorus d k → Real} :
-- imply
  isingTorusDirichlet (isingTorusReflectField i u) = isingTorusDirichlet u := by
-- proof
  apply StatMech.FrontierA.isingTorusDirichlet_reflectField i u

/--
[isingTorusReflectField_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusReflection.lean)
-/
@[path]
private lemma isingTorusReflectField_add_eq
  {d k : Nat}
  {i : Fin d}
  {u v : IsingDyadicTorus d k → Real} :
-- imply
  isingTorusReflectField i (u + v) = isingTorusReflectField i u + isingTorusReflectField i v := by
-- proof
  apply StatMech.FrontierA.isingTorusReflectField_add i u v

/--
[isingTorusDirichletBilinear_reflectField](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusReflection.lean)
-/
@[path]
private lemma isingTorusDirichletBilinear_reflectField_eq
  {d k : Nat}
  {i : Fin d}
  {u v : IsingDyadicTorus d k → Real} :
-- imply
  isingTorusDirichletBilinear (isingTorusReflectField i u) (isingTorusReflectField i v) = isingTorusDirichletBilinear u v := by
-- proof
  apply StatMech.FrontierA.isingTorusDirichletBilinear_reflectField i u v

/--
[isingTorusEmbedUpper_eq_reflect_embedLower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusReflection.lean)
-/
@[path]
private lemma isingTorusEmbedUpper_eq_reflect_embedLower_eq
  {d k : Nat}
  {i : Fin d}
-- given
  (u : IsingTorusLowerSite (k := k) i → Real) :
-- imply
  isingTorusEmbedUpper i u = isingTorusReflectField i (isingTorusEmbedLower i u) := by
-- proof
  apply StatMech.FrontierA.isingTorusEmbedUpper_eq_reflect_embedLower i u

/--
[isingTorusUpperHalfWeight_eq_lowerHalfWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusReflection.lean)
-/
@[path]
private lemma isingTorusUpperHalfWeight_eq_lowerHalfWeight_eq
  {d k : Nat}
  {i : Fin d}
  {beta : Real}
-- given
  (u : IsingTorusLowerSite (k := k) i → Real) :
-- imply
  isingTorusUpperHalfWeight i beta u = isingTorusLowerHalfWeight i beta u := by
-- proof
  apply StatMech.FrontierA.isingTorusUpperHalfWeight_eq_lowerHalfWeight i beta u

/--
[isingTorus_upperFeatureDot_eq_lowerFeatureDot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusReflection.lean)
-/
@[path]
private lemma isingTorus_upperFeatureDot_eq_lowerFeatureDot_eq
  {d k : Nat}
  {i : Fin d}
-- given
  (u v : IsingTorusLowerSite (k := k) i → Real) :
-- imply
  (∑ e : IsingTorusDirectedEdge d k, isingTorusUpperGradientFeature i u e * isingTorusUpperGradientFeature i v e) = ∑ e : IsingTorusDirectedEdge d k, isingTorusLowerGradientFeature i u e * isingTorusLowerGradientFeature i v e := by
-- proof
  apply StatMech.FrontierA.isingTorus_upperFeatureDot_eq_lowerFeatureDot i u v

/--
[isingTorusShiftedPartition_eq_halves](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusReflection.lean)
-/
@[path]
private lemma isingTorusShiftedPartition_eq_halves_eq
  {d k : Nat}
  {i : Fin d}
  {beta : Real}
-- given
  (h : IsingDyadicTorus d k → Real) :
-- imply
  isingTorusShiftedPartition beta h = ∑ lower : ConfigSpace (IsingTorusLowerSite (k := k) i), ∑ upper : ConfigSpace (IsingTorusLowerSite (k := k) i), isingTorusLowerHalfWeight i beta (isingTorusLowerValues i h lower) * isingTorusUpperHalfWeight i beta (isingTorusUpperValues i h upper) * Real.exp (beta * ∑ e : IsingTorusDirectedEdge d k, isingTorusBoundaryFeature i (isingTorusLowerValues i h lower) e * isingTorusBoundaryFeature i (isingTorusUpperValues i h upper) e) := by
-- proof
  apply StatMech.FrontierA.isingTorusShiftedPartition_eq_halves i beta h

/--
[isingTorusLowerValues_polarizeLower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusReflection.lean)
-/
@[path]
private lemma isingTorusLowerValues_polarizeLower_eq
  {d k : Nat}
  {i : Fin d}
-- given
  (h : IsingDyadicTorus d k → Real)
  (sigma : ConfigSpace (IsingTorusLowerSite (k := k) i)) :
-- imply
  isingTorusLowerValues i (isingTorusPolarizeLower i h) sigma = isingTorusLowerValues i h sigma := by
-- proof
  apply StatMech.FrontierA.isingTorusLowerValues_polarizeLower i h sigma

/--
[isingTorusUpperValues_polarizeLower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusReflection.lean)
-/
@[path]
private lemma isingTorusUpperValues_polarizeLower_eq
  {d k : Nat}
  {i : Fin d}
-- given
  (h : IsingDyadicTorus d k → Real)
  (sigma : ConfigSpace (IsingTorusLowerSite (k := k) i)) :
-- imply
  isingTorusUpperValues i (isingTorusPolarizeLower i h) sigma = isingTorusLowerValues i h sigma := by
-- proof
  apply StatMech.FrontierA.isingTorusUpperValues_polarizeLower i h sigma

/--
[isingTorusLowerValues_polarizeUpper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusReflection.lean)
-/
@[path]
private lemma isingTorusLowerValues_polarizeUpper_eq
  {d k : Nat}
  {i : Fin d}
-- given
  (h : IsingDyadicTorus d k → Real)
  (sigma : ConfigSpace (IsingTorusLowerSite (k := k) i)) :
-- imply
  isingTorusLowerValues i (isingTorusPolarizeUpper i h) sigma = isingTorusUpperValues i h sigma := by
-- proof
  apply StatMech.FrontierA.isingTorusLowerValues_polarizeUpper i h sigma

/--
[isingTorusUpperValues_polarizeUpper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusReflection.lean)
-/
@[path]
private lemma isingTorusUpperValues_polarizeUpper_eq
  {d k : Nat}
  {i : Fin d}
-- given
  (h : IsingDyadicTorus d k → Real)
  (sigma : ConfigSpace (IsingTorusLowerSite (k := k) i)) :
-- imply
  isingTorusUpperValues i (isingTorusPolarizeUpper i h) sigma = isingTorusUpperValues i h sigma := by
-- proof
  apply StatMech.FrontierA.isingTorusUpperValues_polarizeUpper i h sigma

/--
[isingTorusShiftedPartition_polarization](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusReflection.lean)
-/
@[path]
private lemma isingTorusShiftedPartition_polarization_eq
  {d k : Nat}
  {i : Fin d}
  {beta : Real}
-- given
  (hbeta : 0 ≤ beta)
  (h : IsingDyadicTorus d k → Real) :
-- imply
  2 * isingTorusShiftedPartition beta h ≤ isingTorusShiftedPartition beta (isingTorusPolarizeLower i h) + isingTorusShiftedPartition beta (isingTorusPolarizeUpper i h) := by
-- proof
  apply StatMech.FrontierA.isingTorusShiftedPartition_polarization i beta hbeta h


-- created on 2026-10-23
