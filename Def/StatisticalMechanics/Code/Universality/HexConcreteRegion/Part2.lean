/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexConcreteRegion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexPairingMaps.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexConcreteRegion.Part2


namespace StatMech.Universality

open Complex

open Function

open HexWalk

open scoped BigOperators


noncomputable def hexConcreteV0 (a : ℂ) (h0 : ℤ) : ℂ := a + halfStep h0


noncomputable def hexConcreteVq (a : ℂ) (h0 : ℤ) : ℂ :=
  a + halfStep h0 + halfStep (h0 + (-1)) + halfStep (h0 + (-1))


noncomputable def hexConcreteVr (a : ℂ) (h0 : ℤ) : ℂ :=
  a + halfStep h0 + halfStep (h0 + 1) + halfStep (h0 + 1)


end StatMech.Universality
