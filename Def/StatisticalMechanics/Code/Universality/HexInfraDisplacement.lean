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


namespace StatMech.Universality

open HexWalk List

open scoped BigOperators Real


noncomputable def hexInfra_midAccum (m : ℂ) (h : ℤ) : List ℤ → ℂ
  | [] => m
  | t :: ts => hexInfra_midAccum (m + HexWalk.halfStep h + HexWalk.halfStep (h + t)) (h + t) ts

end StatMech.Universality
