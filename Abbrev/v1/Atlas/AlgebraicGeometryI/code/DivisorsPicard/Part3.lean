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
public import Def.v1.Atlas.AlgebraicGeometryI.code.DivisorsPicard.Part3


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/DivisorsPicard.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
noncomputable section

open scoped nonZeroDivisors

namespace DivisorsPicard

/-- The Picard group as the quotient `DC / principals`, the abelian group from
Cor 19. -/
abbrev PicardGroupQuot (A : Type*) [CommRing A] [IsDomain A]
    [IsDedekindDomain A] (K : Type*) [Field K] [Algebra A K]
    [IsFractionRing A K] :=
  (FractionalIdeal A⁰ K)ˣ ⧸ PrincipalCartierDivisors A K

end DivisorsPicard
end
