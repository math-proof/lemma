/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteStripEnum.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexConcreteRegion.Part5
import Theorem.StatisticalMechanics.Code.Universality.HexBoundaryAssign.Part3
import Def.StatisticalMechanics.Code.Universality.HexFiniteStripEnum.Part5


namespace StatMech.Universality

open Complex

open HexWalk

open scoped BigOperators


@[simp] theorem hexStrip_singleRegion_mids (a : ℂ) :
    (hexStrip_singleRegion a).mids = ({a} : Finset ℂ) := rfl

@[simp] theorem hexStrip_singleRegion_start (a : ℂ) :
    (hexStrip_singleRegion a).start = a := rfl

end StatMech.Universality
