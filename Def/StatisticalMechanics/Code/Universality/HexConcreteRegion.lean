/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexConcreteRegion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexPairingMaps.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexConcreteRegion


namespace StatMech.Universality

open Complex

open Function

open HexWalk

open scoped BigOperators


noncomputable def hexConcreteV (a : ℂ) (h0 : ℤ) : ℂ := a + halfStep h0


noncomputable def hexConcreteDu (_a : ℂ) (h0 : ℤ) : ℂ := -halfStep h0


noncomputable def hexConcreteQ (a : ℂ) (h0 : ℤ) : ℂ :=
  hexConcreteV a h0 + hexOmega * hexConcreteDu a h0


noncomputable def hexConcreteR (a : ℂ) (h0 : ℤ) : ℂ :=
  hexConcreteV a h0 + hexOmega ^ 2 * hexConcreteDu a h0


end StatMech.Universality
