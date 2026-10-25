/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fc_bulkfraction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.QuadrantPartition.Part9
import Theorem.StatisticalMechanics.Code.FK.InfiniteVolume.Part7
open Filter Topology

open StatMech.FK


namespace StatMech.Walls

variable {d : ℕ}


def fc_T (m n : ℕ) : ℕ := (2 * n + 1) / (2 * m + 1)


end StatMech.Walls
