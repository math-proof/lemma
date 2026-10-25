import Mathlib
import sympy.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.ArithmeticGeometricGenus
open ArithmeticGeometricGenus


namespace ArithmeticGeometricGenus

/--
[arithmeticGenusP1_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ArithmeticGeometricGenus.lean)
-/
@[path]
lemma arithmeticGenusP1_eq_zero
  {k : Type}
  [Field k] :
-- imply
  arithmeticGenusP1 k = 0 := by
-- proof
  unfold arithmeticGenusP1
  exact SheafCohomology.finrank_H1_of_nonneg k 0 le_rfl

end ArithmeticGeometricGenus

namespace ArithmeticGeometricGenus

/--
[geometricGenusP1_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ArithmeticGeometricGenus.lean)
-/
@[path]
lemma geometricGenusP1_eq_zero
  {k : Type}
  [Field k] :
-- imply
  geometricGenusP1 k = 0 := by
-- proof
  unfold geometricGenusP1
  exact SheafCohomology.finrank_H0_of_neg k (-2) (by norm_num)

end ArithmeticGeometricGenus

namespace ArithmeticGeometricGenus

/--
[arith_eq_geom_genus_P1](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ArithmeticGeometricGenus.lean)
-/
@[path]
lemma arith_eq_geom_genus_P1
  {k : Type}
  [Field k] :
-- imply
  arithmeticGenusP1 k = geometricGenusP1 k := by
-- proof
  unfold arithmeticGenusP1 geometricGenusP1
  exact SheafCohomology.serre_duality_nonneg k 0 le_rfl

end ArithmeticGeometricGenus

namespace ArithmeticGeometricGenus

/--
[cor29_arithmetic_eq_geometric_genus](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ArithmeticGeometricGenus.lean)
-/
@[path]
lemma cor29_arithmetic_eq_geometric_genus
  [Field k]
  {C : DedekindCurve k}
  {H1_O : Type*}
  [AddCommGroup H1_O]
  [Module k H1_O]
  [FiniteDimensional k H1_O]
  [FiniteDimensional k (Ω[C.A⁄k])]
-- given
  (hSD : H1_O ≃ₗ[k] Module.Dual k (Ω[C.A⁄k])) :
-- imply
  Module.finrank k H1_O = Module.finrank k (Ω[C.A⁄k]) := by
-- proof
  rw [LinearEquiv.finrank_eq hSD, Subspace.dual_finrank_eq]

end ArithmeticGeometricGenus

namespace ArithmeticGeometricGenus

/--
[cor29_arith_genus_eq_ddGenus](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ArithmeticGeometricGenus.lean)
-/
@[path]
lemma cor29_arith_genus_eq_ddGenus
  [Field k]
  {C : DedekindCurve k}
  {H1_O : Type*}
  [AddCommGroup H1_O]
  [Module k H1_O]
  [FiniteDimensional k H1_O]
  [FiniteDimensional k (Ω[C.A⁄k])]
-- given
  (hSD : H1_O ≃ₗ[k] Module.Dual k (Ω[C.A⁄k])) :
-- imply
  Module.finrank k H1_O = C.ddGenus := by
-- proof
  unfold DedekindCurve.ddGenus
  exact cor29_arithmetic_eq_geometric_genus C H1_O hSD

end ArithmeticGeometricGenus

namespace ArithmeticGeometricGenus

/--
[serre_duality_numerical_P1](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ArithmeticGeometricGenus.lean)
-/
@[path]
lemma serre_duality_numerical_P1
  [Field k]
  {k : Type}
  [Field k]
  {n : ℤ} :
-- imply
  Module.finrank k (SheafCohomology.H1 k n) = Module.finrank k (SheafCohomology.H0 k (-2 - n)) := by
-- proof
  by_cases hn : 0 ≤ n
  · exact SheafCohomology.serre_duality_nonneg k n hn
  · exact SheafCohomology.serre_duality_neg k n (not_le.mp hn)

end ArithmeticGeometricGenus

namespace ArithmeticGeometricGenus

/--
[euler_char_eq_one_minus_arithmeticGenus_P1](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ArithmeticGeometricGenus.lean)
-/
@[path]
lemma euler_char_eq_one_minus_arithmeticGenus_P1
  [Field k]
  {k : Type}
  [Field k] :
-- imply
  (Module.finrank k (SheafCohomology.H0 k 0) : ℤ) - (Module.finrank k (SheafCohomology.H1 k 0) : ℤ) = 1 - (arithmeticGenusP1 k : ℤ) := by
-- proof
  simp only [arithmeticGenusP1,
    SheafCohomology.finrank_H0_of_nonneg k 0 le_rfl,
    SheafCohomology.finrank_H1_of_nonneg k 0 le_rfl]
  norm_num

end ArithmeticGeometricGenus


-- created on 2026-10-23
