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


noncomputable section

open scoped nonZeroDivisors

open IsDedekindDomain

namespace LocallyFactorialDivisors

/-- A ring `R` is locally factorial if all of its localizations at prime ideals
are unique factorization monoids. -/
def IsLocallyFactorial (R : Type*) [CommRing R] [IsDomain R] : Prop :=
  ∀ (P : Ideal R) [P.IsPrime], UniqueFactorizationMonoid (Localization.AtPrime P)

end LocallyFactorialDivisors
end
