/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CartierDivisorGroup.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.RingTheory.ClassGroup
set_option maxHeartbeats 1600000


section CartierDivisorGroupAlgebraic

open scoped nonZeroDivisors

open FractionalIdeal

variable (A : Type*) [CommRing A] [IsDomain A] [IsDedekindDomain A]

variable (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]

/-- The Cartier divisor group of a Dedekind domain `A` with fraction field `K`, defined
algebraically as the units in the monoid of fractional ideals (cf. Def 30, Lec 14). -/
def CartierDivisorGroup : Type _ := (FractionalIdeal A⁰ K)ˣ

end CartierDivisorGroupAlgebraic
