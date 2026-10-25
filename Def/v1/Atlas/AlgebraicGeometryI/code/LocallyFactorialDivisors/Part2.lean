/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/LocallyFactorialDivisors.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.PID
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.ClassGroup
import Mathlib.Data.Finsupp.Basic
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.GroupTheory.QuotientGroup.Basic
import Abbrev.v1.Atlas.AlgebraicGeometryI.code.LocallyFactorialDivisors


noncomputable section

open scoped nonZeroDivisors

open IsDedekindDomain

namespace LocallyFactorialDivisors

attribute [instance] HeightOnePrime.isPrime

/-- Identification between `HeightOnePrime` and Mathlib's `HeightOneSpectrum`. -/
def heightOnePrimeEquiv (R : Type*) [CommRing R] [IsDomain R] :
    HeightOnePrime R ≃ IsDedekindDomain.HeightOneSpectrum R where
  toFun v := ⟨v.asIdeal, v.isPrime, v.ne_bot⟩
  invFun v := ⟨v.asIdeal, v.isPrime, v.ne_bot⟩
  left_inv v := by cases v; rfl
  right_inv v := by cases v; rfl

/-- The additive equivalence between the local `WeilDivisorGroup` and the version
indexed by Mathlib's `HeightOneSpectrum`. -/
def weilDivisorEquiv (R : Type*) [CommRing R] [IsDomain R] :
    WeilDivisorGroup R ≃+ (IsDedekindDomain.HeightOneSpectrum R →₀ ℤ) :=
  Finsupp.domCongr (heightOnePrimeEquiv R)

/-- Convert a fractional ideal to a Weil divisor by taking valuations at each
height-one prime. -/
def fractionalIdealToWeil (I : FractionalIdeal R⁰ K) :
    HeightOneSpectrum R →₀ ℤ :=
  Finsupp.ofSupportFinite
    (fun v => FractionalIdeal.count K v I)
    (Set.Finite.subset (Filter.eventually_cofinite.mp (I.finite_factors))
      (fun v hv => by simp only [Function.mem_support, Set.mem_setOf_eq] at *; exact hv))

end LocallyFactorialDivisors
end
