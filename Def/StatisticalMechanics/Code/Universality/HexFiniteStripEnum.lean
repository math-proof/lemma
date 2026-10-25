/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteStripEnum.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexConcreteRegion.Part5
import Theorem.StatisticalMechanics.Code.Universality.HexBoundaryAssign.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexFiniteStripEnum


namespace StatMech.Universality

open Complex

open HexWalk

open scoped BigOperators


noncomputable def hexStrip_verts (M : Finset ℂ) : Finset ℂ :=
  M.biUnion (fun mm => {mm + halfStep 0, mm + halfStep 1, mm + halfStep 2,
    mm + halfStep 3, mm + halfStep 4, mm + halfStep 5})


end StatMech.Universality
