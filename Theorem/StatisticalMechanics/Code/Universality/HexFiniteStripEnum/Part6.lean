module
public import Theorem.StatisticalMechanics.Code.Universality.HexConcreteRegion.Part5
public import Theorem.StatisticalMechanics.Code.Universality.HexBoundaryAssign.Part3
public import Def.StatisticalMechanics.Code.Universality.HexFiniteStripEnum.Part5


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteStripEnum.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Universality

open Complex

open HexWalk

open scoped BigOperators


@[simp] theorem hexStrip_singleRegion_mids (a : ℂ) :
    (hexStrip_singleRegion a).mids = ({a} : Finset ℂ) := rfl

@[simp] theorem hexStrip_singleRegion_start (a : ℂ) :
    (hexStrip_singleRegion a).start = a := rfl

end StatMech.Universality
