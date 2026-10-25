/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteStripEnum.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexConcreteRegion.Part5
import Theorem.StatisticalMechanics.Code.Universality.HexBoundaryAssign.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexFiniteStripEnum.Part4


namespace StatMech.Universality

open Complex

open HexWalk

open scoped BigOperators


def hexStrip_inStrip (R : HexRegion) (z : ℂ) : Prop :=
  0 ≤ z.re ∧ z.re ≤ R.width ∧ Real.sqrt 3 * |z.im| ≤ R.slant + z.re


noncomputable def hexStrip_region_finiteRegion (R : HexRegion) (M : Finset ℂ)
    (ha : R.start ∈ M) : HexFiniteRegion :=
  hexStrip_finiteRegion M R.start ha

end StatMech.Universality
