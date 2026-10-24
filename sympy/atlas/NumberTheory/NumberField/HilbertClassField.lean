/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/HilbertClassField.lean -/

import Mathlib.FieldTheory.Galois.Abelian
import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.Unramified.Locus

/-!
# Hilbert class fields of number fields

This file introduces the predicate `NumberField.IsHilbertClassField K L`, expressing the
finite number-field characterization of the Hilbert class field of `K`: `L / K` is a
finite-dimensional abelian Galois extension, unramified at every finite height-one prime of
`𝓞 K` and at every infinite place, and maximal with this property.

Maximality means that every finite-dimensional abelian Galois number field `M / K` which is
unramified at every finite height-one prime of `𝓞 K` and at infinite places admits a
`K`-algebra embedding `M →ₐ[K] L`.

The maximality quantifier ranges over competitors `M` in the same universe as `K` and `L`.
This keeps the predicate a single `Prop` without an extra universe parameter while remaining
faithful to the informal characterization. No existence, uniqueness, ray-class-field
equivalence, or concrete instances are asserted here.
-/

open scoped NumberField

namespace NumberField

universe u

/-- Finite number-field characterization of the Hilbert class field of `K`.

`L` is the Hilbert class field of `K` if `L / K` is finite-dimensional abelian Galois,
unramified at every finite height-one prime of `𝓞 K` and at infinite places, and maximal
among such extensions: every other finite-dimensional abelian Galois number field `M / K`
unramified at all finite and infinite places embeds into `L` over `K`. -/
structure IsHilbertClassField (K L : Type u) [Field K] [Field L] [NumberField K]
    [NumberField L] [Algebra K L] : Prop where
  /-- `L / K` is finite-dimensional. -/
  finiteDimensional : FiniteDimensional K L
  /-- `L / K` is abelian Galois. -/
  isAbelianGalois : IsAbelianGalois K L
  /-- Every finite height-one prime of `𝓞 K` is unramified in `𝓞 L`. -/
  isUnramified_finite :
    ∀ 𝔭 : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      Algebra.IsUnramifiedIn (𝓞 L) 𝔭.asIdeal
  /-- `L / K` is unramified at every infinite place. -/
  isUnramified_infinite : IsUnramifiedAtInfinitePlaces K L
  /-- Maximality: every admissible competitor `M / K` embeds into `L` over `K`. -/
  maximal : ∀ (M : Type u) [Field M] [NumberField M] [Algebra K M],
    FiniteDimensional K M →
    IsAbelianGalois K M →
    (∀ 𝔭 : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      Algebra.IsUnramifiedIn (𝓞 M) 𝔭.asIdeal) →
    IsUnramifiedAtInfinitePlaces K M →
    Nonempty (M →ₐ[K] L)

variable {K L : Type u} [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L]
end NumberField
