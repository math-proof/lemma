import Mathlib
import sympy.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.Lec9Blowups.Part3
open Polynomial Lec9Blowups


namespace Lec9Blowups

/--
[blowupAlgebra.monomial_mem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec9Blowups.lean)
-/
@[path]
lemma blowupAlgebra.monomial_mem
  [CommRing A]
  {𝔪 : Ideal A}
  {n : ℕ}
  {a : A} :
-- imply
  monomial n a ∈ blowupAlgebra A 𝔪 ↔ a ∈ 𝔪 ^ n :=
-- proof
  reesAlgebra.monomial_mem

end Lec9Blowups

namespace Lec9Blowups

/--
[blowupMapRestrict_val](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec9Blowups.lean)
-/
@[path]
lemma blowupMapRestrict_val
  [CommRing R]
  [CommRing A]
  {φ : R →+* A}
  {𝔪 : Ideal A}
  {f : blowupAlgebra R (𝔪.comap φ)} :
-- imply
  ((blowupMapRestrict φ 𝔪) f).val = Polynomial.map φ f.val := by
-- proof
  simp [blowupMapRestrict, RingHom.restrict]

end Lec9Blowups

/--
[mem_blowupAlgebra_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec9Blowups.lean)
-/
@[path]
private lemma mem_blowupAlgebra_iff_eq
  [CommRing A]
  {𝔪 : Ideal A}
  {f : A[X]} :
-- imply
  f ∈ blowupAlgebra A 𝔪 ↔ ∀ i, f.coeff i ∈ 𝔪 ^ i := by
-- proof
  apply Lec9Blowups.mem_blowupAlgebra_iff f

/--
[map_mem_blowupAlgebra](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec9Blowups.lean)
-/
@[path]
private lemma map_mem_blowupAlgebra_eq
  [CommRing R]
  [CommRing A]
  {φ : R →+* A}
  {𝔪 : Ideal A}
  {f : R[X]}
-- given
  (hf : f ∈ blowupAlgebra R (𝔪.comap φ)) :
-- imply
  f.map φ ∈ blowupAlgebra A 𝔪 := by
-- proof
  apply Lec9Blowups.map_mem_blowupAlgebra φ 𝔪 f hf

/--
[blowupMapRestrict_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec9Blowups.lean)
-/
@[path]
private lemma blowupMapRestrict_surjective_eq
  [CommRing R]
  [CommRing A]
  {φ : R →+* A}
  {𝔪 : Ideal A}
-- given
  (hφ : Function.Surjective φ) :
-- imply
  Function.Surjective (blowupMapRestrict φ 𝔪) := by
-- proof
  apply Lec9Blowups.blowupMapRestrict_surjective φ hφ 𝔪


-- created on 2026-10-23
