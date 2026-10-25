/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc4_nbrfinite.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Walls.bc4_nbrfinite
open Set SimpleGraph Finset
open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Walls

variable {d : ℕ}


noncomputable def bc4_nbrKey [NeZero d] (n : Site d) : Fin d × Bool := by
  classical
  by_cases h : ∑ j, (n j).natAbs = 1
  · exact ((bc4_witness_coord n h).choose,
      decide (n ((bc4_witness_coord n h).choose) = 1))
  · exact (⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩, false)


end Walls
end StatMech
