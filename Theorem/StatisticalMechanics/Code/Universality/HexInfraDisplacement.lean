/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexInfraDisplacement.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexLattice.Part11
import Theorem.StatisticalMechanics.Code.Universality.HexWall3.Part4
import Def.StatisticalMechanics.Code.Universality.HexInfraDisplacement


namespace StatMech.Universality

open HexWalk List

open scoped BigOperators Real


@[simp] theorem hexInfra_midAccum_nil (m : ℂ) (h : ℤ) : hexInfra_midAccum m h [] = m := rfl

@[simp] theorem hexInfra_midAccum_cons (m : ℂ) (h t : ℤ) (ts : List ℤ) :
    hexInfra_midAccum m h (t :: ts)
      = hexInfra_midAccum (m + HexWalk.halfStep h + HexWalk.halfStep (h + t)) (h + t) ts := rfl


end StatMech.Universality
