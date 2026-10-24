/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/DedekindDomain/FactorizationEquiv.lean -/

import Mathlib.RingTheory.DedekindDomain.Factorization

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

open scoped nonZeroDivisors

open IsDedekindDomain

namespace FractionalIdeal

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

variable (K)

/-- The finite set of height-one primes at which the valuation of `u` is nonzero. -/
noncomputable def unitsSupportFinset (u : (FractionalIdeal R⁰ K)ˣ) :
    Finset (HeightOneSpectrum R) :=
  (Filter.eventually_cofinite.mp (finite_factors (u : FractionalIdeal R⁰ K))).toFinset

theorem mem_unitsSupportFinset (u : (FractionalIdeal R⁰ K)ˣ) (v : HeightOneSpectrum R) :
    v ∈ unitsSupportFinset K u ↔ count K v (u : FractionalIdeal R⁰ K) ≠ 0 := by
  unfold unitsSupportFinset
  exact Set.Finite.mem_toFinset _

/-- The prime exponents of a unit fractional ideal, as a finitely supported function. -/
noncomputable def unitsToFinsupp (u : (FractionalIdeal R⁰ K)ˣ) :
    HeightOneSpectrum R →₀ ℤ :=
  Finsupp.onFinset (unitsSupportFinset K u) (fun v => count K v (u : FractionalIdeal R⁰ K))
    (fun v hv => (mem_unitsSupportFinset K u v).mpr hv)

@[simp]
theorem unitsToFinsupp_apply (u : (FractionalIdeal R⁰ K)ˣ) (v : HeightOneSpectrum R) :
    unitsToFinsupp K u v = count K v (u : FractionalIdeal R⁰ K) :=
  rfl

/-- The finite product of prime powers prescribed by `e` is nonzero. -/
theorem finsuppProd_ne_zero (e : HeightOneSpectrum R →₀ ℤ) :
    e.prod (fun v n => (v.asIdeal : FractionalIdeal R⁰ K) ^ n) ≠ 0 := by
  rw [Finsupp.prod_ne_zero_iff]
  intro v _
  exact zpow_ne_zero _ (coeIdeal_ne_zero.mpr v.ne_bot)

/-- Reconstruction of a unit fractional ideal from prime exponents. -/
noncomputable def finsuppToUnits (e : HeightOneSpectrum R →₀ ℤ) :
    (FractionalIdeal R⁰ K)ˣ :=
  Units.mk0 _ (finsuppProd_ne_zero K e)

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

/-- The bundled multiplicative equivalence between unit fractional ideals and
finitely supported prime-exponent functions. -/
noncomputable def factorizationMulEquiv :
    (FractionalIdeal R⁰ K)ˣ ≃* Multiplicative (HeightOneSpectrum R →₀ ℤ) where
  toFun u := Multiplicative.ofAdd (unitsToFinsupp K u)
  invFun e := finsuppToUnits K (Multiplicative.toAdd e)
  left_inv u := by
    change finsuppToUnits K
      (Multiplicative.toAdd (Multiplicative.ofAdd (unitsToFinsupp K u))) = u
    rw [toAdd_ofAdd]
    exact toUnits_left_inv K u
  right_inv e := by
    change Multiplicative.ofAdd
      (unitsToFinsupp K (finsuppToUnits K (Multiplicative.toAdd e))) = e
    rw [toUnits_right_inv, ofAdd_toAdd]
  map_mul' u v := by
    rw [← ofAdd_add, unitsToFinsupp_mul]
end FractionalIdeal
