import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusSpinReflection.Part2
open Finset StatMech StatMech.FrontierA


/--
[isingTorusHalfReflectionForm_add_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusSpinReflection.lean)
-/
@[path]
private lemma isingTorusHalfReflectionForm_add_left_eq
  {d k : Nat}
  {i : Fin d}
  {beta : Real}
-- given
  (F G H : ConfigSpace (IsingTorusLowerSite (k := k) i) → Real) :
-- imply
  isingTorusHalfReflectionForm i beta (F + G) H = isingTorusHalfReflectionForm i beta F H + isingTorusHalfReflectionForm i beta G H := by
-- proof
  apply StatMech.FrontierA.isingTorusHalfReflectionForm_add_left i beta F G H

/--
[isingTorusHalfReflectionForm_smul_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusSpinReflection.lean)
-/
@[path]
private lemma isingTorusHalfReflectionForm_smul_left_eq
  {d k : Nat}
  {i : Fin d}
  {beta t : Real}
-- given
  (F G : ConfigSpace (IsingTorusLowerSite (k := k) i) → Real) :
-- imply
  isingTorusHalfReflectionForm i beta (t • F) G = t * isingTorusHalfReflectionForm i beta F G := by
-- proof
  apply StatMech.FrontierA.isingTorusHalfReflectionForm_smul_left i beta t F G

/--
[isingTorusHalfReflectionForm_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusSpinReflection.lean)
-/
@[path]
private lemma isingTorusHalfReflectionForm_symm_eq
  {d k : Nat}
  {i : Fin d}
  {beta : Real}
-- given
  (F G : ConfigSpace (IsingTorusLowerSite (k := k) i) → Real) :
-- imply
  isingTorusHalfReflectionForm i beta F G = isingTorusHalfReflectionForm i beta G F := by
-- proof
  apply StatMech.FrontierA.isingTorusHalfReflectionForm_symm i beta F G

/--
[isingTorusHalfReflectionForm_add_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusSpinReflection.lean)
-/
@[path]
private lemma isingTorusHalfReflectionForm_add_right_eq
  {d k : Nat}
  {i : Fin d}
  {beta : Real}
-- given
  (F G H : ConfigSpace (IsingTorusLowerSite (k := k) i) → Real) :
-- imply
  isingTorusHalfReflectionForm i beta F (G + H) = isingTorusHalfReflectionForm i beta F G + isingTorusHalfReflectionForm i beta F H := by
-- proof
  apply StatMech.FrontierA.isingTorusHalfReflectionForm_add_right i beta F G H

/--
[isingTorusHalfReflectionForm_smul_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusSpinReflection.lean)
-/
@[path]
private lemma isingTorusHalfReflectionForm_smul_right_eq
  {d k : Nat}
  {i : Fin d}
  {beta t : Real}
-- given
  (F G : ConfigSpace (IsingTorusLowerSite (k := k) i) → Real) :
-- imply
  isingTorusHalfReflectionForm i beta F (t • G) = t * isingTorusHalfReflectionForm i beta F G := by
-- proof
  apply StatMech.FrontierA.isingTorusHalfReflectionForm_smul_right i beta t F G

/--
[isingTorusHalfReflectionForm_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusSpinReflection.lean)
-/
@[path]
private lemma isingTorusHalfReflectionForm_nonneg_eq
  {d k : Nat}
  {i : Fin d}
  {beta : Real}
-- given
  (hbeta : 0 ≤ beta)
  (F : ConfigSpace (IsingTorusLowerSite (k := k) i) → Real) :
-- imply
  0 ≤ isingTorusHalfReflectionForm i beta F F := by
-- proof
  apply StatMech.FrontierA.isingTorusHalfReflectionForm_nonneg i beta hbeta F

/--
[isingTorusHalfReflectionForm_cauchy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusSpinReflection.lean)
-/
@[path]
private lemma isingTorusHalfReflectionForm_cauchy_eq
  {d k : Nat}
  {i : Fin d}
  {beta : Real}
-- given
  (hbeta : 0 ≤ beta)
  (F G : ConfigSpace (IsingTorusLowerSite (k := k) i) → Real) :
-- imply
  isingTorusHalfReflectionForm i beta F G ^ 2 ≤ isingTorusHalfReflectionForm i beta F F * isingTorusHalfReflectionForm i beta G G := by
-- proof
  apply StatMech.FrontierA.isingTorusHalfReflectionForm_cauchy i beta hbeta F G

/--
[isingTorusHalfReflectionForm_spin_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusSpinReflection.lean)
-/
@[path]
private lemma isingTorusHalfReflectionForm_spin_eq_eq
  {d k : Nat}
  {i : Fin d}
  {beta : Real}
-- given
  (x y : IsingTorusLowerSite (k := k) i) :
-- imply
  isingTorusHalfReflectionForm i beta (isingTorusHalfSpin x) (isingTorusHalfSpin y) = ∑ sigma : ConfigSpace (IsingDyadicTorus d k), Real.exp (-(beta / 2) * isingTorusDirichlet (isingTorusSpinField sigma)) * isingTorusSpinField sigma x.1 * isingTorusSpinField sigma (isingTorusReflectSite i y.1) := by
-- proof
  apply StatMech.FrontierA.isingTorusHalfReflectionForm_spin_eq i beta x y

/--
[isingTorusTwoPoint_reflection_cauchy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusSpinReflection.lean)
-/
@[path]
private lemma isingTorusTwoPoint_reflection_cauchy_eq
  {d k : Nat}
  {i : Fin d}
  {beta : Real}
-- given
  (hbeta : 0 ≤ beta)
  (x y : IsingTorusLowerSite (k := k) i) :
-- imply
  isingTorusTwoPoint beta x.1 (isingTorusReflectSite i y.1) ^ 2 ≤ isingTorusTwoPoint beta x.1 (isingTorusReflectSite i x.1) * isingTorusTwoPoint beta y.1 (isingTorusReflectSite i y.1) := by
-- proof
  apply StatMech.FrontierA.isingTorusTwoPoint_reflection_cauchy i beta hbeta x y

/--
[isingTorusTwoPoint_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusSpinReflection.lean)
-/
@[path]
private lemma isingTorusTwoPoint_symm_eq
  {d k : Nat}
  {beta : Real}
  {x y : IsingDyadicTorus d k} :
-- imply
  isingTorusTwoPoint beta x y = isingTorusTwoPoint beta y x := by
-- proof
  apply StatMech.FrontierA.isingTorusTwoPoint_symm beta x y

/--
[isingTorusTwoPoint_origin_neg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusSpinReflection.lean)
-/
@[path]
private lemma isingTorusTwoPoint_origin_neg_eq
  {d k : Nat}
  {beta : Real}
  {z : IsingDyadicTorus d k} :
-- imply
  isingTorusTwoPoint beta 0 (-z) = isingTorusTwoPoint beta 0 z := by
-- proof
  apply StatMech.FrontierA.isingTorusTwoPoint_origin_neg beta z

/--
[isingTorusCoordinateShift_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusSpinReflection.lean)
-/
@[path]
private lemma isingTorusCoordinateShift_add_eq
  {d k : Nat}
  {i : Fin d}
  {a b : Nat} :
-- imply
  isingTorusCoordinateShift (k := k) i (a + b) = isingTorusCoordinateShift i a + isingTorusCoordinateShift i b := by
-- proof
  apply StatMech.FrontierA.isingTorusCoordinateShift_add i a b

/--
[isingTorusCoordinateShift_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusSpinReflection.lean)
-/
@[path]
private lemma isingTorusCoordinateShift_one_eq
  {d k : Nat}
  {i : Fin d} :
-- imply
  isingTorusCoordinateShift (k := k) i 1 = isingTorusStep i := by
-- proof
  apply StatMech.FrontierA.isingTorusCoordinateShift_one i

/--
[isingTorusReflectSite_coordinateShift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusSpinReflection.lean)
-/
@[path]
private lemma isingTorusReflectSite_coordinateShift_eq
  {d k : Nat}
  {i : Fin d}
  {n : Nat} :
-- imply
  isingTorusReflectSite i (isingTorusCoordinateShift (k := k) i n) = -isingTorusCoordinateShift i n - isingTorusStep i := by
-- proof
  apply StatMech.FrontierA.isingTorusReflectSite_coordinateShift i n

/--
[isingTorusTwoPoint_axis_midpoint_sq_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusSpinReflection.lean)
-/
@[path]
private lemma isingTorusTwoPoint_axis_midpoint_sq_le_eq
  {d k : Nat}
  {i : Fin d}
  {beta : Real}
  {a b : Nat}
-- given
  (hbeta : 0 ≤ beta)
  (ha : a < 2 ^ (k + 1))
  (hb : b < 2 ^ (k + 1)) :
-- imply
  isingTorusTwoPoint (k := k) beta 0 (isingTorusCoordinateShift i (a + b + 1)) ^ 2 ≤ isingTorusTwoPoint (k := k) beta 0 (isingTorusCoordinateShift i (2 * a + 1)) * isingTorusTwoPoint (k := k) beta 0 (isingTorusCoordinateShift i (2 * b + 1)) := by
-- proof
  apply StatMech.FrontierA.isingTorusTwoPoint_axis_midpoint_sq_le i beta hbeta a b ha hb


-- created on 2026-10-23
