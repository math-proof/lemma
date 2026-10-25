/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/LinearEquivDivisors.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.ClassGroup
import Mathlib.RingTheory.DedekindDomain.PID
import Mathlib.Data.Finsupp.Basic
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Abbrev.v1.Atlas.AlgebraicGeometryI.code.LinearEquivDivisors


noncomputable section

open scoped nonZeroDivisors

namespace LinearEquivDivisors

/-- A Weil divisor `D` is effective iff all of its coefficients are nonnegative. -/
def WeilDivisor.IsEffective {Y : Type*} (D : WeilDivisorGroup Y) : Prop :=
  ∀ y : Y, 0 ≤ D y

/-- Two Cartier divisors (nonzero ideals of a Dedekind domain) are linearly
equivalent iff they represent the same element of the class group. -/
def CartierDivisor.LinearlyEquivalent (A : Type*) [CommRing A] [IsDomain A]
    [IsDedekindDomain A] (I J : (Ideal A)⁰) : Prop :=
  ClassGroup.mk0 I = ClassGroup.mk0 J


end LinearEquivDivisors
end
