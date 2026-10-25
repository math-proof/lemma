import Mathlib
import sympy.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.CanonicalBundleProjective.Part4
open KaehlerDifferential Module CanonicalSheafDef CanonicalBundleProj
open QCohProjective TwistSheaf


/--
[kahler_mvPolynomial_free](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CanonicalBundleProjective.lean)
-/
@[path]
lemma kahler_mvPolynomial_free
  {k : Type u}
  [Field k]
  {n : ℕ} :
-- imply
  Module.Free (PolyRing k n) (Ω[PolyRing k n⁄k]) :=
-- proof
  inferInstance

/--
[canonicalModule_polyRing_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CanonicalBundleProjective.lean)
-/
@[path]
lemma canonicalModule_polyRing_eq
  {k : Type u}
  [Field k]
  {n : ℕ} :
-- imply
  canonicalModule k (PolyRing k n) (n + 1) = ⋀[PolyRing k n]^(n + 1) (Ω[PolyRing k n⁄k]) :=
-- proof
  rfl

/--
[canonicalModule_polyRing_finrank](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CanonicalBundleProjective.lean)
-/
@[path]
lemma canonicalModule_polyRing_finrank
  {k : Type u}
  [Field k]
  {n : ℕ} :
-- imply
  Module.finrank (PolyRing k n) (↥(canonicalModule k (PolyRing k n) (n + 1))) = 1 :=
-- proof
  canonicalModule_finrank_eq_one k (PolyRing k n) (n + 1)

/--
[canonicalModule_polyRing_free](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CanonicalBundleProjective.lean)
-/
@[path]
lemma canonicalModule_polyRing_free
  {k : Type u}
  [Field k]
  {n : ℕ} :
-- imply
  Module.Free (PolyRing k n) (↥(canonicalModule k (PolyRing k n) (n + 1))) :=
-- proof
  canonicalModule_free k (PolyRing k n) (n + 1)
section CanonicalBundle
variable (k : Type u) [Field k] (n : ℕ)

/--
[topExteriorPower_kahler_finrank](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CanonicalBundleProjective.lean)
-/
@[path]
lemma topExteriorPower_kahler_finrank
  {k : Type u}
  [Field k]
  {n : ℕ} :
-- imply
  Module.finrank (PolyRing k n) (⋀[PolyRing k n]^(n + 1) (Ω[PolyRing k n⁄k])) = 1 := by
-- proof
  rw [exteriorPower.finrank_eq, kahler_mvPolynomial_finrank, Nat.choose_self]

/--
[topExteriorPower_kahler_free](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CanonicalBundleProjective.lean)
-/
@[path]
lemma topExteriorPower_kahler_free
  {k : Type u}
  [Field k]
  {n : ℕ} :
-- imply
  Module.Free (PolyRing k n) (⋀[PolyRing k n]^(n + 1) (Ω[PolyRing k n⁄k])) :=
-- proof
  inferInstance

/--
[exteriorPower_kahler_finrank_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CanonicalBundleProjective.lean)
-/
@[path]
lemma exteriorPower_kahler_finrank_zero
  {k : Type u}
  [Field k]
  {n : ℕ}
  {p : ℕ}
-- given
  (hp : n + 1 < p) :
-- imply
  Module.finrank (PolyRing k n) (⋀[PolyRing k n]^p (Ω[PolyRing k n⁄k])) = 0 := by
-- proof
  rw [exteriorPower.finrank_eq, kahler_mvPolynomial_finrank, Nat.choose_eq_zero_of_lt hp]

/--
[exteriorPower_kahler_finrank](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CanonicalBundleProjective.lean)
-/
@[path]
lemma exteriorPower_kahler_finrank
  {k : Type u}
  [Field k]
  {n : ℕ}
  {p : ℕ} :
-- imply
  Module.finrank (PolyRing k n) (⋀[PolyRing k n]^p (Ω[PolyRing k n⁄k])) = Nat.choose (n + 1) p := by
-- proof
  rw [exteriorPower.finrank_eq, kahler_mvPolynomial_finrank]
end CanonicalBundle
section DirectSumRank
variable (R : Type u) [CommRing R] [Nontrivial R] (n : ℕ)

/--
[finrank_direct_sum_free](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CanonicalBundleProjective.lean)
-/
@[path]
lemma finrank_direct_sum_free
  {R : Type u}
  [CommRing R]
  [Nontrivial R]
  {n : ℕ} :
-- imply
  Module.finrank R (Fin (n + 1) → R) = n + 1 := by
-- proof
  rw [Module.finrank_fin_fun]

/--
[finrank_top_exterior_direct_sum](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CanonicalBundleProjective.lean)
-/
@[path]
lemma finrank_top_exterior_direct_sum
  {R : Type u}
  [CommRing R]
  [Nontrivial R]
  {n : ℕ} :
-- imply
  Module.finrank R (⋀[R]^(n + 1) (Fin (n + 1) → R)) = 1 := by
-- proof
  rw [exteriorPower.finrank_eq, Module.finrank_fin_fun, Nat.choose_self]
end DirectSumRank
namespace CanonicalBundleProj
open QCohProjective TwistSheaf
variable (k : Type u) [Field k] (n : ℕ)

namespace CanonicalBundleProj

/--
[det_direct_sum_twist](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CanonicalBundleProjective.lean)
-/
@[path]
lemma det_direct_sum_twist
  {k : Type u}
  [Field k]
  {n : ℕ} :
-- imply
  (n + 1 : ℤ) * (-1 : ℤ) = -(↑n + 1 : ℤ) := by
-- proof
ring

end CanonicalBundleProj

namespace CanonicalBundleProj

/--
[canonical_twist_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CanonicalBundleProjective.lean)
-/
@[path]
lemma canonical_twist_eq
  {k : Type u}
  [Field k]
  {n : ℕ} :
-- imply
  (-(↑n + 1 : ℤ)) = -(↑(n + 1) : ℤ) := by
-- proof
  push_cast; ring

end CanonicalBundleProj

/--
[kahler_mvPolynomial_finrank](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CanonicalBundleProjective.lean)
-/
@[path]
private lemma kahler_mvPolynomial_finrank_eq
  {k : Type u}
  [Field k]
  {n : ℕ} :
-- imply
  Module.finrank (PolyRing k n) (Ω[PolyRing k n⁄k]) = n + 1 := by
-- proof
  apply kahler_mvPolynomial_finrank k n


-- created on 2026-10-23
