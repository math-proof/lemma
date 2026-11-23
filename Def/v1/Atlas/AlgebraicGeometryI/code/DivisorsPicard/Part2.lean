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
public import Abbrev.v1.Atlas.AlgebraicGeometryI.code.DivisorsPicard.Part2

@[expose] public section

noncomputable section

open scoped nonZeroDivisors

namespace DivisorsPicard

/-- The principal divisor map (Def 31, Lec 15) sending a unit of `K` to the
fractional ideal it spans; its image is the subgroup of principal divisors. -/
def principalDivisorMap_Def31 (A : Type*) [CommRing A] [IsDomain A]
    [IsDedekindDomain A] (K : Type*) [Field K] [Algebra A K]
    [IsFractionRing A K] : Kˣ →* (FractionalIdeal A⁰ K)ˣ :=
  toPrincipalIdeal A K

end DivisorsPicard
end
