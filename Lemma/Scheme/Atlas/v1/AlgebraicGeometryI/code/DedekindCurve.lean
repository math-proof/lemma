import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.DedekindCurve
open nonZeroDivisors RiemannRochCurves CanonicalSheafCurves DedekindCurve
open scoped TensorProduct
open RiemannRochCurves CanonicalSheafCurves


/--
[DedekindCurve.h1_O_eq_genus](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/DedekindCurve.lean)
-/
@[path]
lemma DedekindCurve.h1_O_eq_genus
-- imply
  ∀ (k : Type*) [Field k] (A : Type*) [CommRing A] [IsDomain A] [IsDedekindDomain A] [Algebra k A] [Module.Finite k A], DedekindCurve.h1_O k A = Module.finrank k (Ω[A⁄k]) :=
-- proof
  fun _ _ _ _ _ _ _ _ => rfl

/--
[DedekindCurve.h1_sky_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/DedekindCurve.lean)
-/
@[path]
lemma DedekindCurve.h1_sky_eq_zero
-- imply
  ∀ (k : Type*) [Field k] (A : Type*) [CommRing A] [IsDomain A] [IsDedekindDomain A] [Algebra k A] [Module.Finite k A], DedekindCurve.h1_sky k A = 0 :=
-- proof
  fun _ _ _ _ _ _ _ _ => rfl
namespace DedekindCurve
variable {k : Type*} [Field k]

namespace DedekindCurve

/--
[cohChi_struct](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/DedekindCurve.lean)
-/
@[path]
lemma cohChi_struct
  [Field k]
  {C : DedekindCurve k} :
-- imply
  C.cohChi (1, 0) = 1 - (h1_O k C.A : ℤ) := by
-- proof
  simp [cohChi]

end DedekindCurve

namespace DedekindCurve

/--
[cohChi_sky](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/DedekindCurve.lean)
-/
@[path]
lemma cohChi_sky
  [Field k]
  {C : DedekindCurve k} :
-- imply
  C.cohChi (0, 1) = 1 - (h1_sky k C.A : ℤ) := by
-- proof
  simp [cohChi]

end DedekindCurve

namespace DedekindCurve

/--
[cohChi_struct_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/DedekindCurve.lean)
-/
@[path]
lemma cohChi_struct_eq
  [Field k]
  {C : DedekindCurve k} :
-- imply
  C.cohChi (1, 0) = 1 - (C.ddGenus : ℤ) := by
-- proof
  simp only [cohChi_struct, h1_O_eq_genus, ddGenus]

end DedekindCurve

namespace DedekindCurve

/--
[cohChi_sky_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/DedekindCurve.lean)
-/
@[path]
lemma cohChi_sky_eq
  [Field k]
  {C : DedekindCurve k} :
-- imply
  C.cohChi (0, 1) = 1 := by
-- proof
  rw [cohChi_sky, h1_sky_eq_zero]; simp

end DedekindCurve

namespace DedekindCurve

/--
[cohChi_eq_rrHom](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/DedekindCurve.lean)
-/
@[path]
lemma cohChi_eq_rrHom
  [Field k]
  {C : DedekindCurve k} :
-- imply
  C.cohChi = RiemannRochCurves.rrHom (C.ddGenus : ℤ) :=
-- proof
  RiemannRochCurves.additive_homs_eq_of_generators_eq C.cohChi
    (RiemannRochCurves.rrHom (C.ddGenus : ℤ))
    (by rw [C.cohChi_struct_eq, RiemannRochCurves.rr_value_structure_sheaf])
    (by rw [C.cohChi_sky_eq, RiemannRochCurves.rr_value_skyscraper])

end DedekindCurve

namespace DedekindCurve

/--
[eulerCharO_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/DedekindCurve.lean)
-/
@[path]
lemma eulerCharO_eq
  [Field k]
  {C : DedekindCurve k} :
-- imply
  C.eulerCharO = 1 - (C.ddGenus : ℤ) :=
-- proof
  rfl

end DedekindCurve

namespace DedekindCurve

/--
[degK_eq_2g_sub_2](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/DedekindCurve.lean)
-/
@[path]
lemma degK_eq_2g_sub_2
  [Field k]
  {C : DedekindCurve k} :
-- imply
  C.degK = 2 * (C.ddGenus : ℤ) - 2 :=
-- proof
  rfl

end DedekindCurve

namespace DedekindCurve

/--
[toSmoothCompleteCurve_rr](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/DedekindCurve.lean)
-/
@[path]
lemma toSmoothCompleteCurve_rr
  [Field k]
  {C : DedekindCurve k}
  {r d : ℤ} :
-- imply
  C.toSmoothCompleteCurve.χ (r, d) = d - r * ((C.ddGenus : ℤ) - 1) :=
-- proof
  CanonicalSheafCurves.chi_eq_rr C.toSmoothCompleteCurve r d

end DedekindCurve

namespace DedekindCurve

/--
[h1_O_sheaf_eq_genus](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/DedekindCurve.lean)
-/
@[path]
lemma h1_O_sheaf_eq_genus
  [Field k] :
-- imply
  ∀ (k : Type*) [Field k] (A : Type*) [CommRing A] [IsDomain A] [IsDedekindDomain A] [Algebra k A] [Module.Finite k A], h1_O_sheaf k A = Module.finrank k (Ω[A⁄k]) :=
-- proof
  fun _ _ _ _ _ _ _ _ => rfl

end DedekindCurve

namespace DedekindCurve

/--
[eulerCharO_sheaf_eq_formula](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/DedekindCurve.lean)
-/
@[path]
lemma eulerCharO_sheaf_eq_formula
  [Field k] :
-- imply
  ∀ (k : Type*) [Field k] (A : Type*) [CommRing A] [IsDomain A] [IsDedekindDomain A] [Algebra k A] [Module.Finite k A], eulerCharO_sheaf k A = 1 - (Module.finrank k (Ω[A⁄k]) : ℤ) :=
-- proof
  fun _ _ _ _ _ _ _ _ => rfl

end DedekindCurve

namespace DedekindCurve

/--
[degK_sheaf_eq_formula](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/DedekindCurve.lean)
-/
@[path]
lemma degK_sheaf_eq_formula
  [Field k] :
-- imply
  ∀ (k : Type*) [Field k] (A : Type*) [CommRing A] [IsDomain A] [IsDedekindDomain A] [Algebra k A] [Module.Finite k A], degK_sheaf k A = 2 * (Module.finrank k (Ω[A⁄k]) : ℤ) - 2 :=
-- proof
  fun _ _ _ _ _ _ _ _ => rfl

end DedekindCurve


-- created on 2026-10-23
