/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/WeilDivisor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.FreeAbelianGroup.Finsupp
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Abbrev.v1.Atlas.AlgebraicGeometryI.code.WeilDivisor


noncomputable section

namespace WeilDivisor

/-- A Weil divisor is effective iff all of its coefficients are nonnegative. -/
def IsEffective {Y : Type*} (D : WeilDivisor.Group Y) : Prop :=
  ∀ y : Y, 0 ≤ D y


/-- The Weil divisor `n · [D]` consisting of `n` copies of a single
codim-1 subvariety `D`. -/
def single {Y : Type*} (D : Y) (n : ℤ) : WeilDivisor.Group Y :=
  Finsupp.single D n

/-- The coefficient of a Weil divisor `D` along a codim-1 subvariety `y`. -/
def coeff {Y : Type*} (D : WeilDivisor.Group Y) (y : Y) : ℤ :=
  D y


/-- Identification of the Weil divisor group with the abstract free abelian
group on `Y`. -/
def equivFreeAbelianGroup (Y : Type*) :
    WeilDivisor.Group Y ≃+ FreeAbelianGroup Y :=
  (FreeAbelianGroup.equivFinsupp Y).symm


end WeilDivisor
end
