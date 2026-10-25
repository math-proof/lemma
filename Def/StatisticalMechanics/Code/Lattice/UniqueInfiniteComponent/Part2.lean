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
import Theorem.StatisticalMechanics.Code.Lattice.UniqueInfiniteComponent
open Set SimpleGraph


namespace StatMech

namespace Lattice

variable {d : ℕ}


def setOn (p : Site d) (T : Finset (Fin d)) (v : ℤ) : Site d :=
  fun k => if k ∈ T then v else p k

end Lattice
end StatMech
