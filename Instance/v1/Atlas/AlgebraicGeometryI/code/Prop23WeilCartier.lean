/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Prop23WeilCartier.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.UniqueFactorizationDomain.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs

@[expose] public section

set_option autoImplicit false


section Prop23

variable (k : Type*) [Field k]

/-- The formal power series ring `k[[x_1, ..., x_n]]` over a field is a domain. -/
instance mvPowerSeries_fin_isDomain' (n : ℕ) : IsDomain (MvPowerSeries (Fin n) k) :=
  NoZeroDivisors.to_isDomain _

end Prop23
