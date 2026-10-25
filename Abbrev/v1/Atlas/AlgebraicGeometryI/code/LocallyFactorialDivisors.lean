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
import Structure.v1.Atlas.AlgebraicGeometryI.code.LocallyFactorialDivisors


noncomputable section

open scoped nonZeroDivisors

open IsDedekindDomain

namespace LocallyFactorialDivisors

attribute [instance] HeightOnePrime.isPrime

/-- The group of Weil divisors, formal `ℤ`-linear combinations of height-one primes. -/
abbrev WeilDivisorGroup (R : Type*) [CommRing R] [IsDomain R] :=
  HeightOnePrime R →₀ ℤ

/-- The Cartier divisor group, identified with the unit group of fractional
ideals in the fraction field. -/
abbrev CartierDivisorGroup (R : Type*) [CommRing R] [IsDomain R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K] :=
  (FractionalIdeal R⁰ K)ˣ

end LocallyFactorialDivisors
end
