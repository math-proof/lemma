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
import Def.v1.Atlas.AlgebraicGeometryI.code.LocallyFactorialDivisors.Part3


noncomputable section

open scoped nonZeroDivisors

open IsDedekindDomain

namespace LocallyFactorialDivisors

attribute [instance] HeightOnePrime.isPrime

/-- Pointwise formula for `cartierToWeil`. -/
@[simp]
lemma cartierToWeil_apply (u : (FractionalIdeal R⁰ K)ˣ) (v : HeightOneSpectrum R) :
    (cartierToWeil K u) v = FractionalIdeal.count K v (u : FractionalIdeal R⁰ K) := by
  simp [cartierToWeil]


/-- The unit Cartier divisor maps to the zero Weil divisor. -/
theorem cartierToWeil_one :
    cartierToWeil K (1 : (FractionalIdeal R⁰ K)ˣ) = 0 := by
  ext v
  simp [FractionalIdeal.count_one]

/-- `cartierToWeil` is multiplicative: product becomes sum of valuations. -/
theorem cartierToWeil_mul (u₁ u₂ : (FractionalIdeal R⁰ K)ˣ) :
    cartierToWeil K (u₁ * u₂) = cartierToWeil K u₁ + cartierToWeil K u₂ := by
  ext v
  simp only [cartierToWeil_apply, Finsupp.add_apply, Units.val_mul]
  exact FractionalIdeal.count_mul K v (Units.ne_zero u₁) (Units.ne_zero u₂)


/-- The Cartier-to-Weil map is injective: a fractional ideal is determined by its
collection of valuations. -/
theorem cartierToWeil_injective :
    Function.Injective (cartierToWeil (R := R) K) := by
  intro u₁ u₂ h
  have h1 : (u₁ : FractionalIdeal R⁰ K) ≠ 0 := Units.ne_zero u₁
  have h2 : (u₂ : FractionalIdeal R⁰ K) ≠ 0 := Units.ne_zero u₂
  have factored1 := FractionalIdeal.finprod_heightOneSpectrum_factorization' (R := R) K h1
  have factored2 := FractionalIdeal.finprod_heightOneSpectrum_factorization' (R := R) K h2
  have counts_eq : ∀ v : HeightOneSpectrum R,
      FractionalIdeal.count K v (u₁ : FractionalIdeal R⁰ K) =
      FractionalIdeal.count K v (u₂ : FractionalIdeal R⁰ K) := by
    intro v
    have := Finsupp.ext_iff.mp h v
    simp only [cartierToWeil, fractionalIdealToWeil_apply] at this
    exact this
  have val_eq : (u₁ : FractionalIdeal R⁰ K) = (u₂ : FractionalIdeal R⁰ K) := by
    rw [← factored1, ← factored2]
    exact finprod_congr (fun v => by rw [counts_eq v])
  exact Units.val_injective val_eq


end LocallyFactorialDivisors
end
