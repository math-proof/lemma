/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/FiniteRangePerco.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Probability.InhomogeneousProduct.Part2
import Theorem.StatisticalMechanics.Code.Percolation.SubcriticalDecayFull.Part2
import Theorem.StatisticalMechanics.Code.Percolation.SurfaceReassembly
import Theorem.StatisticalMechanics.Code.Sharpness.BkCriterionFull.Part2
import Def.StatisticalMechanics.Code.Sharpness.FiniteRangePerco.Part13
open MeasureTheory
open scoped NNReal


namespace StatMech

namespace Sharpness

open ConfigSpace Lattice Percolation


variable {d : ℕ}


theorem mem_frpShiftedBox (y z : Site d) (n : ℕ) :
    z ∈ frpShiftedBox y n ↔ z + y ∈ box d (n - 1) := by
  classical
  rw [frpShiftedBox, Finset.mem_image]
  constructor
  · rintro ⟨w, hw, rfl⟩
    have hwbox : w ∈ box d (n - 1) := by
      simpa [Set.Finite.mem_toFinset] using hw
    simpa only [sub_add_cancel] using hwbox
  · intro hz
    refine ⟨z + y, ?_, ?_⟩
    · simpa [Set.Finite.mem_toFinset] using hz
    · simp

end Sharpness
end StatMech
