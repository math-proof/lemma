/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/Spectrum/Prime/GroupAction.lean -/

/-
Author: @toskua, Avocado
-/

import Mathlib.RingTheory.Ideal.Pointwise
import Mathlib.RingTheory.Spectrum.Prime.Basic

/-!
# Group actions on prime spectra

The group action on a prime spectrum induced by a group acting
on the underlying commutative semiring by automorphisms is provided
upstream by Mathlib (`MulAction G (PrimeSpectrum R)`). This module retains
the compatibility alias `smul_asIdeal` used within MathlibExt.
-/

open scoped Pointwise

namespace PrimeSpectrum

section Basic

variable {G R : Type*} [Group G] [CommSemiring R] [MulSemiringAction G R]

/-- The underlying ideal of a translated prime is the translated ideal. -/
@[simp]
theorem smul_asIdeal (g : G) (p : PrimeSpectrum R) :
    (g • p).asIdeal = g • p.asIdeal :=
  rfl

end Basic

end PrimeSpectrum
