/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/DedekindDomain/FactorizationEquiv.lean -/

import Mathlib.RingTheory.DedekindDomain.Factorization
import Theorem.RingTheory.DedekindDomain.FactorizationEquiv
open scoped nonZeroDivisors

open IsDedekindDomain

/-!
# Prime-exponent equivalence for fractional ideals of a Dedekind domain

For a Dedekind domain `R` with fraction field `K`, every nonzero fractional ideal
factors uniquely as a finite product of prime powers. This file bundles that
factorization into a multiplicative equivalence between the units of the type of
fractional ideals and the finitely supported prime-exponent functions.

## Main definitions

* `FractionalIdeal.unitsToFinsupp`: sends a unit fractional ideal to its prime
  exponents, via `FractionalIdeal.count`.
* `FractionalIdeal.finsuppToUnits`: reconstructs a unit fractional ideal as the
  finite product of prime powers prescribed by a finitely supported function.
* `FractionalIdeal.factorizationMulEquiv`: the bundled multiplicative
  equivalence `(FractionalIdeal R⁰ K)ˣ ≃* Multiplicative (HeightOneSpectrum R →₀ ℤ)`.

## Main results

* `FractionalIdeal.toUnits_left_inv` and `FractionalIdeal.toUnits_right_inv`:
  the two inverse laws, from `FractionalIdeal.finprod_heightOneSpectrum_factorization'`
  and `FractionalIdeal.count_finsuppProd`.
* `FractionalIdeal.unitsToFinsupp_mul`: valuations add under multiplication, from
  `FractionalIdeal.count_mul`.
-/


namespace FractionalIdeal

variable {R : Type*} [CommRing R] [IsDedekindDomain R]

variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

variable (K)

/-- The prime exponents of a unit fractional ideal, as a finitely supported function. -/
noncomputable def unitsToFinsupp (u : (FractionalIdeal R⁰ K)ˣ) :
    HeightOneSpectrum R →₀ ℤ :=
  Finsupp.onFinset (unitsSupportFinset K u) (fun v => count K v (u : FractionalIdeal R⁰ K))
    (fun v hv => (mem_unitsSupportFinset K u v).mpr hv)

end FractionalIdeal
