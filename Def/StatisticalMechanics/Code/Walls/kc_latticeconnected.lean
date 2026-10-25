/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc_latticeconnected.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.SegmentConn
import Theorem.StatisticalMechanics.Code.Walls.kc_latticeconnected
open Set SimpleGraph


namespace StatMech

namespace Walls

open StatMech.Lattice

variable {d : ℕ}


def kc_merge (x y : Site d) (k : ℕ) : Site d :=
  fun i => if (i : ℕ) < k then y i else x i

end Walls
end StatMech
