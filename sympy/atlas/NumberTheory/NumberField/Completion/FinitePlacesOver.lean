/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/Completion/FinitePlacesOver.lean -/

import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.Ideal.GoingUp

/-!
# Places of a number field extension lying over a fixed finite place

Given a number field extension `L / K` and a finite place `v` of `K`, recorded as
a height-one prime of `𝓞 K`, the finite places of `L` lying over `v` are the
height-one primes of `𝓞 L` lying over `v.asIdeal`. This file names that index type,
identifies it with `Ideal.primesOver`, and transfers finiteness and nonemptiness.

## ATLAS source map

This is a supporting index-type stage toward ATLAS NumberTheoryI item N265, Theorem 13.5,
Section 13.1, primary declaration
`TensorProductDecomposition.theorem_13_5_finite_place_Kv` in
`v1/Atlas/NumberTheoryI/code/GlobalFields.lean` lines 1152--1211. Include:
<https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/GlobalFields.lean#L1152-L1211>.

* The source product is indexed by
  `{w : HeightOneSpectrum (O L) // FinitePlace.LiesAbove w v}` at lines 1156--1165;
  `FinitePlace.LiesAbove` is defined at lines 75--78 by contraction of `w.asIdeal` to
  `v.asIdeal`. Native `v.placesOver L` packages the same condition through
  `w.asIdeal.LiesOver v.asIdeal`.
* Native `placesOverEquivPrimesOver` refines the source map into `Ideal.primesOver` used by
  `TensorProductDecomposition.finitePlacesAbove_finite` at lines 762--771, supplying both
  directions and round-trip laws; `finite_placesOver` transfers the source finiteness, and
  `nonempty_placesOver` transfers Mathlib's nonemptiness of primes above a nonzero prime.
* This module only packages the finite-place index type, its canonical prime-ideal
  equivalence, and finiteness/nonemptiness for later products. It does not construct
  the completion maps or the full tensor-product equivalence of Theorem 13.5.
-/

namespace IsDedekindDomain.HeightOneSpectrum

open scoped NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- Finite places of `L` lying over the finite place `v` of `K`, as height-one
primes of `𝓞 L` lying over `v.asIdeal`. -/
def placesOver (v : HeightOneSpectrum (𝓞 K)) (L : Type*) [Field L] [NumberField L]
    [Algebra K L] : Type _ :=
  { w : HeightOneSpectrum (𝓞 L) // w.asIdeal.LiesOver v.asIdeal }

/-- Canonical identification of `v.placesOver L` with the primes of `𝓞 L` lying
over `v.asIdeal`. -/
noncomputable def placesOverEquivPrimesOver (v : HeightOneSpectrum (𝓞 K)) (L : Type*)
    [Field L] [NumberField L] [Algebra K L] :
    v.placesOver L ≃ v.asIdeal.primesOver (𝓞 L) :=
  { toFun := fun w => ⟨w.val.asIdeal, w.val.isPrime, w.property⟩
    invFun := fun Q =>
      ⟨⟨Q.val, Q.property.1, Ideal.ne_bot_of_mem_primesOver v.ne_bot Q.property⟩,
        Q.property.2⟩
    left_inv := fun _w => Subtype.ext (HeightOneSpectrum.ext rfl)
    right_inv := fun _Q => Subtype.ext rfl }

/-- Only finitely many finite places of `L` lie over `v`. -/
instance finite_placesOver (v : HeightOneSpectrum (𝓞 K)) (L : Type*) [Field L]
    [NumberField L] [Algebra K L] : Finite (v.placesOver L) :=
  Finite.of_equiv _ (v.placesOverEquivPrimesOver L).symm

/-- At least one finite place of `L` lies over `v`. -/
instance nonempty_placesOver (v : HeightOneSpectrum (𝓞 K)) (L : Type*) [Field L]
    [NumberField L] [Algebra K L] : Nonempty (v.placesOver L) :=
  (v.placesOverEquivPrimesOver L).nonempty

end IsDedekindDomain.HeightOneSpectrum
