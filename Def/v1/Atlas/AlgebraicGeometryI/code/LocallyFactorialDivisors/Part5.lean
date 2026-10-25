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
import Theorem.v1.Atlas.AlgebraicGeometryI.code.LocallyFactorialDivisors.Part3


noncomputable section

open scoped nonZeroDivisors

open IsDedekindDomain

namespace LocallyFactorialDivisors

attribute [instance] HeightOnePrime.isPrime

/-- The Cartier-to-Weil map packaged as a monoid homomorphism into the
multiplicative form of the Weil divisor group. -/
def cartierToWeilMonoidHom :
    (FractionalIdeal R⁰ K)ˣ →* Multiplicative (HeightOneSpectrum R →₀ ℤ) where
  toFun u := Multiplicative.ofAdd (cartierToWeil K u)
  map_one' := by rw [cartierToWeil_one, ofAdd_zero]
  map_mul' a b := by rw [cartierToWeil_mul, ofAdd_add]

/-- The Cartier-to-Weil map upgraded to a multiplicative equivalence, assuming
local factoriality. -/
def cartierToWeilMulEquiv (_hlf : IsLocallyFactorial R) :
    (FractionalIdeal R⁰ K)ˣ ≃* Multiplicative (HeightOneSpectrum R →₀ ℤ) :=
  MulEquiv.ofBijective (cartierToWeilMonoidHom K) <| by
    constructor
    ·
      intro u₁ u₂ h
      exact cartierToWeil_injective K h
    ·
      intro m
      obtain ⟨u, hu⟩ := cartierToWeil_surjective K (Multiplicative.toAdd m)
      exact ⟨u, by simp [cartierToWeilMonoidHom, hu]⟩

end LocallyFactorialDivisors
end
