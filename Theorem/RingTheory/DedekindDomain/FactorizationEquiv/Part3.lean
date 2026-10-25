/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/DedekindDomain/FactorizationEquiv.lean -/

import Mathlib.RingTheory.DedekindDomain.Factorization
import Def.RingTheory.DedekindDomain.FactorizationEquiv.Part3
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

/-- Reconstruction after taking exponents is the identity. -/
theorem toUnits_left_inv (u : (FractionalIdeal R⁰ K)ˣ) :
    finsuppToUnits K (unitsToFinsupp K u) = u := by
  refine Units.ext ?_
  have h0 : ∀ v : HeightOneSpectrum R, v ∉ unitsSupportFinset K u →
      (v.asIdeal : FractionalIdeal R⁰ K) ^ count K v (u : FractionalIdeal R⁰ K) = 1 := by
    intro v hv
    have hcount : count K v (u : FractionalIdeal R⁰ K) = 0 := by
      by_contra hne
      exact hv ((mem_unitsSupportFinset K u v).mpr hne)
    rw [hcount, zpow_zero]
  have hsup : Function.mulSupport
      (fun v => (v.asIdeal : FractionalIdeal R⁰ K) ^ count K v (u : FractionalIdeal R⁰ K)) ⊆
      ↑(unitsSupportFinset K u) := by
    intro v hv
    rw [Finset.mem_coe]
    by_contra hcon
    exact hv (h0 v hcon)
  calc (↑(finsuppToUnits K (unitsToFinsupp K u)) : FractionalIdeal R⁰ K)
      = ∏ v ∈ unitsSupportFinset K u,
        (v.asIdeal : FractionalIdeal R⁰ K) ^ count K v (u : FractionalIdeal R⁰ K) :=
        Finsupp.prod_onFinset _ _ _ _ (fun i _ => zpow_zero _)
    _ = ∏ᶠ v, (v.asIdeal : FractionalIdeal R⁰ K) ^ count K v (u : FractionalIdeal R⁰ K) :=
        (finprod_eq_finsetProd_of_mulSupport_subset _ hsup).symm
    _ = (u : FractionalIdeal R⁰ K) := finprod_heightOneSpectrum_factorization' K u.ne_zero

/-- Taking exponents after reconstruction is the identity. -/
theorem toUnits_right_inv (e : HeightOneSpectrum R →₀ ℤ) :
    unitsToFinsupp K (finsuppToUnits K e) = e := by
  ext v
  exact count_finsuppProd K v e

/-- Valuations add under multiplication of fractional ideals. -/
theorem unitsToFinsupp_mul (u v : (FractionalIdeal R⁰ K)ˣ) :
    unitsToFinsupp K (u * v) = unitsToFinsupp K u + unitsToFinsupp K v := by
  ext w
  simp only [unitsToFinsupp_apply, Units.val_mul, Finsupp.add_apply]
  exact count_mul K w u.ne_zero v.ne_zero

end FractionalIdeal
