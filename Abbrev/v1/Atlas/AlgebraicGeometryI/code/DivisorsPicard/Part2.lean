/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/DivisorsPicard.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.ClassGroup
public import Mathlib.RingTheory.DedekindDomain.PID
public import Mathlib.RingTheory.DedekindDomain.Dvr
public import Mathlib.RingTheory.DedekindDomain.Factorization
public import Mathlib.RingTheory.UniqueFactorizationDomain.Kaplansky
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.PowerSeries.Ideal
public import Instance.v1.Atlas.AlgebraicGeometryI.code.DivisorsPicard


@[expose] public noncomputable section

open scoped nonZeroDivisors

namespace DivisorsPicard

/-- The Cartier divisor group `DC(A)` (Def 30, Lec 15), realized as the units of
the monoid of fractional ideals. -/
abbrev CartierDivisorGroupUnits (A : Type*) [CommRing A] [IsDomain A]
    [IsDedekindDomain A] (K : Type*) [Field K] [Algebra A K]
    [IsFractionRing A K] := (FractionalIdeal A⁰ K)ˣ

/-- Alternative spelling of `CartierDivisorGroupUnits` over a general domain. -/
abbrev CartierDivisorGroup' (A : Type*) [CommRing A] [IsDomain A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K] :=
  (FractionalIdeal A⁰ K)ˣ

end DivisorsPicard
end
