/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CartierDivisorGroup.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.RingTheory.ClassGroup
import Instance.v1.Atlas.AlgebraicGeometryI.code.CartierDivisorGroup
set_option maxHeartbeats 1600000


section CartierDivisorGroupAlgebraic

open scoped nonZeroDivisors

open FractionalIdeal

variable (A : Type*) [CommRing A] [IsDomain A] [IsDedekindDomain A]

variable (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]

namespace CartierDivisorGroup

/-- The tautological multiplicative equivalence between `CartierDivisorGroup A K` and the units
of fractional ideals. -/
noncomputable def equiv : CartierDivisorGroup A K ≃* (FractionalIdeal A⁰ K)ˣ :=
  MulEquiv.refl _

/-- Forget the Cartier divisor wrapping to obtain the underlying unit fractional ideal. -/
noncomputable def toUnits (D : CartierDivisorGroup A K) :
    (FractionalIdeal A⁰ K)ˣ := D

/-- View a Cartier divisor as the underlying fractional ideal (forgetting invertibility). -/
noncomputable def toFractionalIdeal (D : CartierDivisorGroup A K) :
    FractionalIdeal A⁰ K :=
  (D.toUnits : FractionalIdeal A⁰ K)

/-- The principal divisor map `Kˣ → CartierDivisorGroup A K` sending a unit `x` to the
divisor of the principal fractional ideal `(x)`. -/
noncomputable def principalDivisor : Kˣ →* CartierDivisorGroup A K :=
  toPrincipalIdeal A K

/-- The Picard group of a Dedekind domain is the quotient of the Cartier divisor group by the
subgroup of principal divisors; this realises it as the ideal class group. -/
noncomputable def picardEquiv :
    ClassGroup A ≃*
      (CartierDivisorGroup A K) ⧸ (principalDivisor A K).range := by
  unfold CartierDivisorGroup principalDivisor
  exact ClassGroup.equiv K

/-- Promote a nonzero ordinary ideal of `A` to a Cartier divisor by viewing it as a fractional
ideal of `K`. -/
noncomputable def fromIdeal : (Ideal A)⁰ →* CartierDivisorGroup A K :=
  FractionalIdeal.mk0 K

end CartierDivisorGroup
end CartierDivisorGroupAlgebraic
