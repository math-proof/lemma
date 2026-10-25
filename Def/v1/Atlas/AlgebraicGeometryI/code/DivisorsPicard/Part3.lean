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
import Theorem.v1.Atlas.AlgebraicGeometryI.code.DivisorsPicard


noncomputable section

open scoped nonZeroDivisors

namespace DivisorsPicard

/-- The subgroup of principal Cartier divisors, i.e. the image of the principal
divisor map. -/
def PrincipalCartierDivisors (A : Type*) [CommRing A] [IsDomain A]
    [IsDedekindDomain A] (K : Type*) [Field K] [Algebra A K]
    [IsFractionRing A K] : Subgroup (FractionalIdeal A⁰ K)ˣ :=
  (toPrincipalIdeal A K).range

end DivisorsPicard
end
