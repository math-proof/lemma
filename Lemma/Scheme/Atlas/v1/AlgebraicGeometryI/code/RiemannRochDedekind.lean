import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.RiemannRochDedekind
open nonZeroDivisors RiemannRochCurves DedekindCurve UniqueFactorizationMonoid RiemannRochDedekind
open scoped TensorProduct
open RiemannRochCurves DedekindCurve
open UniqueFactorizationMonoid


namespace RiemannRochDedekind

/--
[h1_O_eq_genus](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRochDedekind.lean)
-/
@[path]
lemma h1_O_eq_genus
-- imply
  ∀ (k : Type*) [Field k] (A : Type*) [CommRing A] [IsDomain A] [IsDedekindDomain A] [Algebra k A] [Module.Finite k A], h1_O k A = Module.finrank k (Ω[A⁄k]) :=
-- proof
  DedekindCurve.h1_O_eq_genus

end RiemannRochDedekind

namespace RiemannRochDedekind

/--
[h1_sky_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRochDedekind.lean)
-/
@[path]
lemma h1_sky_eq_zero
-- imply
  ∀ (k : Type*) [Field k] (A : Type*) [CommRing A] [IsDomain A] [IsDedekindDomain A] [Algebra k A] [Module.Finite k A], h1_sky k A = 0 :=
-- proof
  DedekindCurve.h1_sky_eq_zero

end RiemannRochDedekind

namespace RiemannRochDedekind

/--
[dedekind_curve_rr](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRochDedekind.lean)
-/
@[path]
lemma dedekind_curve_rr
  [Field k]
  {C : DedekindCurve k}
  {r d : ℤ} :
-- imply
  C.toSmoothCompleteCurve.χ (r, d) = d - r * ((C.ddGenus : ℤ) - 1) :=
-- proof
  C.toSmoothCompleteCurve_rr r d

end RiemannRochDedekind


-- created on 2026-10-23
