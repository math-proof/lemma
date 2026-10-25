/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsAnchorEncode.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.ContourSubsetCount
import Def.StatisticalMechanics.Code.Lattice.PeierlsAnchorEncode.Part3
open Finset Set SimpleGraph


namespace StatMech

namespace Lattice

attribute [local instance] Classical.propDecidable

variable {d : ℕ}


theorem axisAnchorPool_card_le (d ℓ : ℕ) : (axisAnchorPool d ℓ).card ≤ ℓ := by
  classical
  refine le_trans (Finset.card_image_le) ?_
  rw [Finset.card_range]


theorem axisVertex_zero_eq_origin :
    axisVertex d 0 = StatMech.Ising.origin d := by
  funext i
  simp only [axisVertex, StatMech.Ising.origin, Nat.cast_zero]
  split <;> rfl


end Lattice
end StatMech
