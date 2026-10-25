import Mathlib
import sympy.Basic
import Def.NumberTheory.Height.Absolute
open IntermediateField Polynomial
open NumberField


namespace NumberField

/--
[primitiveIntMinpoly_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Height/Absolute.lean)
-/
@[path]
lemma primitiveIntMinpoly_ne_zero
  [Field K] [Algebra ℚ K]
  {x : K} :
-- imply
  primitiveIntMinpoly x ≠ 0 :=
-- proof
  Polynomial.primPart_ne_zero _

end NumberField

namespace NumberField

/--
[primitiveIntMinpoly_isPrimitive](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Height/Absolute.lean)
-/
@[path]
lemma primitiveIntMinpoly_isPrimitive
  [Field K] [Algebra ℚ K]
  {x : K} :
-- imply
  (primitiveIntMinpoly x).IsPrimitive :=
-- proof
  Polynomial.isPrimitive_primPart _

end NumberField

namespace NumberField

/--
[primitiveIntMinpoly_natDegree](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Height/Absolute.lean)
-/
@[path]
lemma primitiveIntMinpoly_natDegree
  [Field K] [Algebra ℚ K]
  {x : K} :
-- imply
  (primitiveIntMinpoly x).natDegree = (minpoly ℚ x).natDegree := by
-- proof
  rw [primitiveIntMinpoly, Polynomial.natDegree_primPart]
  let q := IsLocalization.integerNormalization (nonZeroDivisors ℤ) (minpoly ℚ x)
  have hmap : (q.map (algebraMap ℤ ℚ)).natDegree = q.natDegree :=
    Polynomial.natDegree_map_eq_of_injective Int.cast_injective q
  obtain ⟨b, hb, hspec⟩ :=
    IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) (minpoly ℚ x)
  have hsmul : (b • minpoly ℚ x).natDegree = (minpoly ℚ x).natDegree :=
    Polynomial.natDegree_smul (minpoly ℚ x) (nonZeroDivisors.ne_zero hb)
  rwa [← hmap, hspec]

end NumberField

namespace NumberField

/--
[primitiveIntMinpoly_algHom_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Height/Absolute.lean)
-/
@[path]
lemma primitiveIntMinpoly_algHom_eq
  [Field K] [Algebra ℚ K] [Field L] [Algebra ℚ L]
  {f : K →ₐ[ℚ] L}
  {x : K}
-- given
  (hf : Function.Injective f) :
-- imply
  primitiveIntMinpoly (f x) = primitiveIntMinpoly x := by
-- proof
  simp only [primitiveIntMinpoly, minpoly.algHom_eq f hf x]

end NumberField

namespace NumberField

/--
[absMulHeight₁_pos](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Height/Absolute.lean)
-/
@[path]
lemma absMulHeight₁_pos
  [Field L] [CharZero L]
  {x : L} :
-- imply
  0 < absMulHeight₁ x := by
-- proof
  rw [absMulHeight₁]
  split_ifs with hx
  · let _ : FiniteDimensional ℚ (IntermediateField.adjoin ℚ {x}) :=
    IntermediateField.adjoin.finiteDimensional hx
    let _ : NumberField (IntermediateField.adjoin ℚ {x}) := {}
    exact Real.rpow_pos_of_pos (Height.mulHeight₁_pos _) _
  · exact zero_lt_one

end NumberField

namespace NumberField

/--
[one_le_absMulHeight₁](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Height/Absolute.lean)
-/
@[path]
lemma one_le_absMulHeight₁
  [Field L] [CharZero L]
  {x : L} :
-- imply
  1 ≤ absMulHeight₁ x := by
-- proof
  rw [absMulHeight₁]
  split_ifs with hx
  · let _ : FiniteDimensional ℚ (IntermediateField.adjoin ℚ {x}) :=
    IntermediateField.adjoin.finiteDimensional hx
    let _ : NumberField (IntermediateField.adjoin ℚ {x}) := {}
    exact Real.one_le_rpow (Height.one_le_mulHeight₁ _) (by positivity)
  · rfl

end NumberField

namespace NumberField

/--
[absLogHeight₁_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Height/Absolute.lean)
-/
@[path]
lemma absLogHeight₁_nonneg
  [Field L] [CharZero L]
  {x : L} :
-- imply
  0 ≤ absLogHeight₁ x := by
-- proof
  rw [absLogHeight₁]
  exact Real.log_nonneg (one_le_absMulHeight₁ x)

end NumberField


-- created on 2026-10-20
-- updated on 2026-10-23
