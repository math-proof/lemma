/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/PowerSeriesUFD.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.Ideal
public import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.FieldTheory.RatFunc.Degree
public import Mathlib.RingTheory.RegularLocalRing.Defs

@[expose] public section

set_option backward.isDefEq.respectTransparency false


namespace PowerSeriesUFD

variable (k : Type*) [Field k]

/-- The power series ring k[[x_1,...,x_n]] is an integral domain. -/
instance mvPowerSeries_fin_isDomain (n : ℕ) : IsDomain (MvPowerSeries (Fin n) k) :=
  NoZeroDivisors.to_isDomain _

/-- The power series ring k[[x_1,...,x_n]] is a local ring. -/
instance mvPowerSeries_fin_isLocalRing (n : ℕ) : IsLocalRing (MvPowerSeries (Fin n) k) :=
  inferInstance

end PowerSeriesUFD
