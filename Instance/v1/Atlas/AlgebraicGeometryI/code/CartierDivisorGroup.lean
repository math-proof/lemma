/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CartierDivisorGroup.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.RingTheory.ClassGroup
public import Def.v1.Atlas.AlgebraicGeometryI.code.CartierDivisorGroup

@[expose] public section

set_option maxHeartbeats 1600000


section CartierDivisorGroupAlgebraic

open scoped nonZeroDivisors

open FractionalIdeal

variable (A : Type*) [CommRing A] [IsDomain A] [IsDedekindDomain A]

variable (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]

namespace CartierDivisorGroup

/-- The Cartier divisor group is a commutative group, inherited from the units of fractional
ideals. -/
noncomputable instance instCommGroup : CommGroup (CartierDivisorGroup A K) :=
  inferInstanceAs (CommGroup (FractionalIdeal A⁰ K)ˣ)

/-- The Cartier divisor group is inhabited by the trivial divisor `1`. -/
noncomputable instance instInhabited : Inhabited (CartierDivisorGroup A K) := ⟨1⟩

end CartierDivisorGroup
end CartierDivisorGroupAlgebraic
