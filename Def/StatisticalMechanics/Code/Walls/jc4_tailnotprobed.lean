/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc4_tailnotprobed.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.jc3_earfootprint.Part3
import Theorem.StatisticalMechanics.Code.Walls.jc3_core.Part2
import Theorem.StatisticalMechanics.Code.Lattice.BalancePreservingContraction.Part4
open SimpleGraph Function


namespace StatMech

namespace Walls

open StatMech.Lattice


def jc4_TailFootprintFree (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (r : Site 2) (m n : ℕ) : Prop :=
  ∀ i, i < n → jc3_AvoidsEarFootprint r ((dartNext K)^[m + i] a.1)


end Walls
end StatMech
