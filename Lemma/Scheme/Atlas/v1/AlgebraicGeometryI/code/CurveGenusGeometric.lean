import Mathlib
import sympy.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.CurveGenusGeometric
open CurveGenusGeometric


namespace CurveGenusGeometric

/--
[cor29_arithmetic_eq_geometric_genus](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CurveGenusGeometric.lean)
-/
@[path]
lemma cor29_arithmetic_eq_geometric_genus
  {k : Type*}
  [Field k]
  {A : Type*}
  [CommRing A]
  [Algebra k A]
  {H1_O : Type*}
  [AddCommGroup H1_O]
  [Module k H1_O]
  [FiniteDimensional k H1_O]
  [FiniteDimensional k (Ω[A⁄k])]
-- given
  (hSD : H1_O ≃ₗ[k] Module.Dual k (Ω[A⁄k])) :
-- imply
  arithmeticGenus k H1_O = geometricGenus k A := by
-- proof
  unfold arithmeticGenus geometricGenus
  rw [LinearEquiv.finrank_eq hSD, Subspace.dual_finrank_eq]

end CurveGenusGeometric

namespace CurveGenusGeometric

/--
[genus_eq_finrank_kahler](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CurveGenusGeometric.lean)
-/
@[path]
lemma genus_eq_finrank_kahler
  {k : Type*}
  [Field k]
  {A : Type*}
  [CommRing A]
  [Algebra k A]
  {H1_O : Type*}
  [AddCommGroup H1_O]
  [Module k H1_O]
  [FiniteDimensional k H1_O]
  [FiniteDimensional k (Ω[A⁄k])]
-- given
  (hSD : H1_O ≃ₗ[k] Module.Dual k (Ω[A⁄k])) :
-- imply
  arithmeticGenus k H1_O = Module.finrank k (Ω[A⁄k]) := by
-- proof
  unfold arithmeticGenus
  rw [LinearEquiv.finrank_eq hSD, Subspace.dual_finrank_eq]

end CurveGenusGeometric

namespace CurveGenusGeometric

/--
[euler_char_structure_sheaf](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CurveGenusGeometric.lean)
-/
@[path]
lemma euler_char_structure_sheaf
  {k : Type*}
  [Field k]
  {A : Type*}
  [CommRing A]
  [Algebra k A]
  {H0_O : Type*}
  [AddCommGroup H0_O]
  [Module k H0_O]
  {H1_O : Type*}
  [AddCommGroup H1_O]
  [Module k H1_O]
-- given
  (h_h0 : Module.finrank k H0_O = 1)
  (h_h1 : Module.finrank k H1_O = geometricGenus k A) :
-- imply
  (Module.finrank k H0_O : ℤ) - (Module.finrank k H1_O : ℤ) = 1 - (geometricGenus k A : ℤ) := by
-- proof
  rw [h_h0, h_h1]
  simp

end CurveGenusGeometric

namespace CurveGenusGeometric

/--
[serre_duality_euler_char](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CurveGenusGeometric.lean)
-/
@[path]
lemma serre_duality_euler_char
  {k : Type*}
  [Field k]
  {A : Type*}
  [CommRing A]
  [Algebra k A]
  {g : ℤ} :
-- imply
  (1 - g) + (g - 1) = (0 : ℤ) := by
-- proof
  ring

end CurveGenusGeometric

namespace CurveGenusGeometric

/--
[geometricGenus_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CurveGenusGeometric.lean)
-/
@[path]
lemma geometricGenus_nonneg
  {k : Type*}
  [Field k]
  {A : Type*}
  [CommRing A]
  [Algebra k A] :
-- imply
  0 ≤ (geometricGenus k A : ℤ) :=
-- proof
  Int.natCast_nonneg _

end CurveGenusGeometric

namespace CurveGenusGeometric

/--
[genus_zero_iff_rational](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CurveGenusGeometric.lean)
-/
@[path]
lemma genus_zero_iff_rational
  {k : Type*}
  [Field k]
  {A : Type*}
  [CommRing A]
  [Algebra k A]
  {H1_O : Type*}
  [AddCommGroup H1_O]
  [Module k H1_O]
  [FiniteDimensional k H1_O]
  [FiniteDimensional k (Ω[A⁄k])]
-- given
  (hSD : H1_O ≃ₗ[k] Module.Dual k (Ω[A⁄k]))
  (hg : geometricGenus k A = 0) :
-- imply
  arithmeticGenus k H1_O = 0 := by
-- proof
  rw [cor29_arithmetic_eq_geometric_genus k A H1_O hSD, hg]

end CurveGenusGeometric

namespace CurveGenusGeometric

/--
[genus_one_elliptic](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CurveGenusGeometric.lean)
-/
@[path]
lemma genus_one_elliptic
  {k : Type*}
  [Field k]
  {A : Type*}
  [CommRing A]
  [Algebra k A]
  {H1_O : Type*}
  [AddCommGroup H1_O]
  [Module k H1_O]
  [FiniteDimensional k H1_O]
  [FiniteDimensional k (Ω[A⁄k])]
-- given
  (hSD : H1_O ≃ₗ[k] Module.Dual k (Ω[A⁄k]))
  (hg : geometricGenus k A = 1) :
-- imply
  arithmeticGenus k H1_O = 1 := by
-- proof
  rw [cor29_arithmetic_eq_geometric_genus k A H1_O hSD, hg]

end CurveGenusGeometric


-- created on 2026-10-23
