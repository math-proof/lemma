module
public import Mathlib.RingTheory.DedekindDomain.Factorization
public import Mathlib.RingTheory.DedekindDomain.PID
public import Mathlib.RingTheory.DedekindDomain.Dvr
public import Mathlib.RingTheory.ClassGroup
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Def.v1.Atlas.AlgebraicGeometryI.code.LocallyFactorialDivisors.Part6


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/LocallyFactorialDivisors.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
noncomputable section

open scoped nonZeroDivisors

open IsDedekindDomain

namespace LocallyFactorialDivisors

attribute [instance] HeightOnePrime.isPrime

/-- The Weil divisor class group, Weil divisors modulo principal Weil divisors. -/
abbrev WeilDivisorClassGroup (R : Type*) [CommRing R] [IsDomain R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    (e : CartierDivisorGroup R K ≃* Multiplicative (WeilDivisorGroup R)) :=
  Multiplicative (WeilDivisorGroup R) ⧸ PrincipalWeilDivisors R K e


end LocallyFactorialDivisors
end
