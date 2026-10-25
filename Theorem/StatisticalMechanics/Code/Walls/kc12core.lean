/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc12core.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.kc10core.Part3
import Theorem.StatisticalMechanics.Code.Walls.kc6uniqueinfinitecomponent
import Theorem.StatisticalMechanics.Code.Lattice.ExteriorConnected.Part3
import Theorem.StatisticalMechanics.Code.Lattice.InsideConnected.Part2
open Set SimpleGraph Function


namespace StatMech

namespace Walls

open StatMech.Lattice

variable {a : Site 2}


theorem kc12_farLeftBeacon_mem_exterior (R : ℕ) :
    (![-((R : ℤ) + 1), 0] : Site 2) ∈ exterior 2 R :=
  exc_farLeft_mem_exterior R


theorem kc12_far_mem_exterior (R : ℕ) {w : Site 2} (hw : w 0 ≤ -((R : ℤ) + 1)) :
    w ∈ exterior 2 R :=
  ⟨0, by omega⟩


end Walls
end StatMech
