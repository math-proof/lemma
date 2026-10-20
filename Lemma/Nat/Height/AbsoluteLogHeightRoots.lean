import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Height.AbsoluteLogHeightRoots
open Polynomial
open MathlibExt.NumberTheory.Height.AbsoluteWanted


/--
[absLogHeight](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Height/AbsoluteLogHeightRoots.lean)
-/
@[path]
private lemma absLogHeight_eq
  [Field K] [CharZero K] [Algebra ℚ K]
  {x : K}
-- given
  (hx : IsIntegral ℚ x) :
-- imply
  NumberField.absLogHeight₁ x =
    (Real.log
    ‖((NumberField.primitiveIntMinpoly x).map (Int.castRingHom ℂ)).leadingCoeff‖ +
    (((NumberField.primitiveIntMinpoly x).map (Int.castRingHom ℂ)).roots.map
    (fun z => Real.posLog ‖z‖)).sum) /
    ((minpoly ℚ x).natDegree : ℝ) := by
-- proof
  apply MathlibExt.NumberTheory.Height.AbsoluteWanted.absLogHeight x hx

/--
[absLogHeight](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Height/AbsoluteLogHeightRoots.lean)
-/
@[path]
private lemma MathlibExt_NumberTheory_Height_AbsoluteWanted_absLogHeight_eq
  [Field K] [CharZero K] [Algebra ℚ K]
  {x : K}
-- given
  (hx : IsIntegral ℚ x) :
-- imply
  NumberField.absLogHeight₁ x =
    (Real.log
    ‖((NumberField.primitiveIntMinpoly x).map (Int.castRingHom ℂ)).leadingCoeff‖ +
    (((NumberField.primitiveIntMinpoly x).map (Int.castRingHom ℂ)).roots.map
    (fun z => Real.posLog ‖z‖)).sum) /
    ((minpoly ℚ x).natDegree : ℝ) := by
-- proof
  apply MathlibExt.NumberTheory.Height.AbsoluteWanted.absLogHeight x hx

/--
[absLogHeight](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Height/AbsoluteLogHeightRoots.lean)
-/
@[path]
private lemma MathlibExt_NumberTheory_Height_AbsoluteWanted_absLogHeight_eq
  [Field K] [CharZero K] [Algebra ℚ K]
  {x : K}
-- given
  (hx : IsIntegral ℚ x) :
-- imply
  NumberField.absLogHeight₁ x =
    (Real.log
    ‖((NumberField.primitiveIntMinpoly x).map (Int.castRingHom ℂ)).leadingCoeff‖ +
    (((NumberField.primitiveIntMinpoly x).map (Int.castRingHom ℂ)).roots.map
    (fun z => Real.posLog ‖z‖)).sum) /
    ((minpoly ℚ x).natDegree : ℝ) := by
-- proof
  apply MathlibExt.NumberTheory.Height.AbsoluteWanted.absLogHeight x hx

/--
[absMulHeight](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Height/AbsoluteLogHeightRoots.lean)
-/
@[path]
private lemma absMulHeight_eq
  [Field K] [CharZero K] [Algebra ℚ K]
  {x : K}
-- given
  (hx : IsIntegral ℚ x) :
-- imply
  NumberField.absMulHeight₁ x =
    (NumberField.primitiveIntMinpoly x).mapMahlerMeasure (Int.castRingHom ℂ) ^
    ((minpoly ℚ x).natDegree : ℝ)⁻¹ := by
-- proof
  apply MathlibExt.NumberTheory.Height.AbsoluteWanted.absMulHeight x hx

/--
[absMulHeight](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Height/AbsoluteLogHeightRoots.lean)
-/
@[path]
private lemma MathlibExt_NumberTheory_Height_AbsoluteWanted_absMulHeight_eq
  [Field K] [CharZero K] [Algebra ℚ K]
  {x : K}
-- given
  (hx : IsIntegral ℚ x) :
-- imply
  NumberField.absMulHeight₁ x =
    (NumberField.primitiveIntMinpoly x).mapMahlerMeasure (Int.castRingHom ℂ) ^
    ((minpoly ℚ x).natDegree : ℝ)⁻¹ := by
-- proof
  apply MathlibExt.NumberTheory.Height.AbsoluteWanted.absMulHeight x hx


-- created on 2026-10-20
