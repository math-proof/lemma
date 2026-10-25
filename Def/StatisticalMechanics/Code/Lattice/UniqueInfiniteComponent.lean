/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/UniqueInfiniteComponent.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.SegmentConn
open Set SimpleGraph


namespace StatMech

namespace Lattice

variable {d : ℕ}


def exterior (d R : ℕ) : Set (Site d) := {x | ∃ i, R < (x i).natAbs}

end Lattice
end StatMech
