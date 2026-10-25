/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/DivisorsPicard.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.ClassGroup
import Mathlib.RingTheory.DedekindDomain.PID
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.UniqueFactorizationDomain.Kaplansky
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.Data.Finsupp.Basic
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.PowerSeries.Ideal
import Abbrev.v1.Atlas.AlgebraicGeometryI.code.DivisorsPicard


noncomputable section

open scoped nonZeroDivisors

namespace DivisorsPicard

/-- A Weil divisor is effective when all coefficients are non-negative. -/
def WeilDivisor.IsEffective {Y : Type*} (D : WeilDivisorGroup Y) : Prop :=
  ∀ y : Y, 0 ≤ D y


/-- Two Cartier divisors (i.e. non-zero ideals) are linearly equivalent when they
represent the same class in the Picard group. -/
def CartierDivisor.LinearlyEquivalent (A : Type*) [CommRing A] [IsDomain A]
    [IsDedekindDomain A] (I J : (Ideal A)⁰) : Prop :=
  ClassGroup.mk0 I = ClassGroup.mk0 J


/-- The Cartier-to-Weil divisor map: send a fractional ideal to its valuation
data, recording for each height-one prime the order of vanishing. -/
def cartierToWeilDivisor (R : Type*) [CommRing R] [IsDomain R] [IsDedekindDomain R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    (I : FractionalIdeal R⁰ K) :
    WeilDivisorGroup (IsDedekindDomain.HeightOneSpectrum R) :=
  Finsupp.ofSupportFinite (fun v => FractionalIdeal.count K v I) (by
    have h := FractionalIdeal.finite_factors I
    rw [Filter.eventually_cofinite] at h
    exact h.subset fun v hv => hv)

/-- Restriction of the Cartier-to-Weil map to invertible fractional ideals. -/
def cartierToWeilFun (I : (FractionalIdeal R⁰ K)ˣ) :
    WeilDivisorGroup (IsDedekindDomain.HeightOneSpectrum R) :=
  Finsupp.ofSupportFinite (fun v => FractionalIdeal.count K v I.val) (by
    have h := FractionalIdeal.finite_factors (I : FractionalIdeal R⁰ K)
    rw [Filter.eventually_cofinite] at h
    exact h.subset fun v hv => hv)

variable (R : Type*) [CommRing R] [IsDomain R] [IsDedekindDomain R]
         (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K] in
/-- The Weil-to-Cartier map: build an invertible fractional ideal as the product
of prime ideals raised to the orders specified by the Weil divisor. -/
def weilToCartierFun (D : WeilDivisorGroup (IsDedekindDomain.HeightOneSpectrum R)) :
    (FractionalIdeal R⁰ K)ˣ :=
  Units.mk0 (D.prod (fun v n => (v.asIdeal : FractionalIdeal R⁰ K) ^ n)) (by
    rw [Finsupp.prod, Finset.prod_ne_zero_iff]
    intro v _
    exact zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr v.ne_bot))

/-- The multiplicative isomorphism between invertible fractional ideals (the
Cartier divisor group) and the free abelian group on height-one primes (the
Weil divisor group), proving `DC ≃ DW` for a Dedekind domain. -/
def cartierWeilIso (R : Type*) [CommRing R] [IsDomain R] [IsDedekindDomain R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K] :
    (FractionalIdeal R⁰ K)ˣ ≃*
      Multiplicative (WeilDivisorGroup (IsDedekindDomain.HeightOneSpectrum R)) where
  toFun I := Multiplicative.ofAdd (cartierToWeilFun R K I)
  invFun D := weilToCartierFun R K (Multiplicative.toAdd D)
  left_inv I := by
    show weilToCartierFun R K (cartierToWeilFun R K I) = I
    ext1
    simp only [weilToCartierFun, Units.val_mk0]
    have key := FractionalIdeal.finprod_heightOneSpectrum_factorization' (K := K) (Units.ne_zero I)
    rw [Finsupp.prod]; symm; rw [← key]
    apply finprod_eq_prod_of_mulSupport_subset
    intro v hv
    rw [Function.mem_mulSupport] at hv
    simp only [Finset.mem_coe, Finsupp.mem_support_iff, cartierToWeilFun,
      Finsupp.ofSupportFinite_coe, ne_eq]
    intro h; exact hv (by rw [h, zpow_zero])
  right_inv D := by
    show Multiplicative.ofAdd
      (cartierToWeilFun R K (weilToCartierFun R K (Multiplicative.toAdd D))) = D
    apply Multiplicative.ext
    show cartierToWeilFun R K (weilToCartierFun R K (Multiplicative.toAdd D)) =
      Multiplicative.toAdd D
    ext v
    simp only [cartierToWeilFun, Finsupp.ofSupportFinite_coe, weilToCartierFun, Units.val_mk0]
    exact FractionalIdeal.count_finsuppProd K v (Multiplicative.toAdd D)
  map_mul' I J := by
    show Multiplicative.ofAdd (cartierToWeilFun R K (I * J)) =
      Multiplicative.ofAdd (cartierToWeilFun R K I) *
        Multiplicative.ofAdd (cartierToWeilFun R K J)
    rw [← ofAdd_add]; apply Multiplicative.ext
    show cartierToWeilFun R K (I * J) =
      cartierToWeilFun R K I + cartierToWeilFun R K J
    ext v
    simp only [cartierToWeilFun, Units.val_mul, Finsupp.ofSupportFinite_coe,
      Finsupp.coe_add, Pi.add_apply,
      FractionalIdeal.count_mul K v (Units.ne_zero I) (Units.ne_zero J)]

/-- `Pic(R) = DC(R) / principals`: the class group is isomorphic to the
quotient of invertible fractional ideals by principal fractional ideals
(Cor 19, Lec 15). -/
def picIsomCartierQuotPrincipal (R : Type*) [CommRing R] [IsDomain R]
    [IsDedekindDomain R] (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K] :
    ClassGroup R ≃* (FractionalIdeal R⁰ K)ˣ ⧸ (toPrincipalIdeal R K).range :=
  ClassGroup.equiv K


/-- A ring is locally factorial when each localization at a prime ideal is a UFD;
the hypothesis under which Weil and Cartier divisors agree. -/
def IsLocallyFactorial (R : Type*) [CommRing R] [IsDomain R] : Prop :=
  ∀ (P : Ideal R) [P.IsPrime], UniqueFactorizationMonoid (Localization.AtPrime P)

end DivisorsPicard
end
