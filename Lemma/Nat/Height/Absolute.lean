import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Height.Absolute
open IntermediateField Polynomial
open NumberField


/--
[primitiveIntMinpoly_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Height/Absolute.lean)
-/
@[path]
private lemma primitiveIntMinpoly_ne_zero_eq
  [Field K] [Algebra ℚ K]
  {x : K} :
-- imply
  primitiveIntMinpoly x ≠ 0 := by
-- proof
  apply NumberField.primitiveIntMinpoly_ne_zero x

/--
[primitiveIntMinpoly_isPrimitive](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Height/Absolute.lean)
-/
@[path]
private lemma primitiveIntMinpoly_isPrimitive_eq
  [Field K] [Algebra ℚ K]
  {x : K} :
-- imply
  (primitiveIntMinpoly x).IsPrimitive := by
-- proof
  apply NumberField.primitiveIntMinpoly_isPrimitive x

/--
[primitiveIntMinpoly_natDegree](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Height/Absolute.lean)
-/
@[path]
private lemma primitiveIntMinpoly_natDegree_eq
  [Field K] [Algebra ℚ K]
  {x : K} :
-- imply
  (primitiveIntMinpoly x).natDegree = (minpoly ℚ x).natDegree := by
-- proof
  apply NumberField.primitiveIntMinpoly_natDegree x

/--
[primitiveIntMinpoly_algHom_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Height/Absolute.lean)
-/
@[path]
private lemma primitiveIntMinpoly_algHom_eq_eq
  [Field K] [Algebra ℚ K] [Field L] [Algebra ℚ L]
  {f : K →ₐ[ℚ] L}
  {x : K}
-- given
  (hf : Function.Injective f) :
-- imply
  primitiveIntMinpoly (f x) = primitiveIntMinpoly x := by
-- proof
  apply NumberField.primitiveIntMinpoly_algHom_eq f hf x

/--
[absMulHeight](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Height/Absolute.lean)
-/
@[path]
private lemma absMulHeight_eq
  [Field K] [Algebra ℚ K] [Field L] [CharZero L]
  {x : L} :
-- imply
  0 < absMulHeight₁ x := by
-- proof
  apply NumberField.absMulHeight x

/--
[one_le_absMulHeight](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Height/Absolute.lean)
-/
@[path]
private lemma one_le_absMulHeight_eq
  [Field K] [Algebra ℚ K] [Field L] [CharZero L]
  {x : L} :
-- imply
  1 ≤ absMulHeight₁ x := by
-- proof
  apply NumberField.one_le_absMulHeight x

/--
[absLogHeight](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Height/Absolute.lean)
-/
@[path]
private lemma absLogHeight_eq
  [Field K] [Algebra ℚ K] [Field L] [CharZero L]
  {x : L} :
-- imply
  0 ≤ absLogHeight₁ x := by
-- proof
  apply NumberField.absLogHeight x


-- created on 2026-10-20
