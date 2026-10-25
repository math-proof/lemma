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
import Def.StatisticalMechanics.Code.Sharpness.FiniteRangePerco.Part6
open MeasureTheory
open scoped NNReal


namespace StatMech

namespace Sharpness

open ConfigSpace Lattice Percolation


variable {d : ℕ}


theorem mem_frpBoundaryPairs (K : FiniteRangeKernel d) (S : Finset (Site d))
    {x y : Site d} :
    (x, y) ∈ frpBoundaryPairs K S ↔
      x ∈ S ∧ y ∉ S ∧ (frpGraph K).Adj x y := by
  classical
  rw [frpBoundaryPairs, Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨⟨⟨a, z⟩, haz, hmap⟩, hyS⟩
    rw [Finset.mem_product] at haz
    simp only [Prod.mk.injEq] at hmap
    rcases hmap with ⟨rfl, rfl⟩
    refine ⟨haz.1, hyS, ?_⟩
    change 0 < K.coupling ((a + z) - a)
    rw [add_sub_cancel_left]
    exact (mem_frpSteps K).mp haz.2
  · rintro ⟨hxS, hyS, hxy⟩
    let z := y - x
    have hz : z ∈ frpSteps K := (mem_frpSteps K).mpr hxy
    have hsum : x + z = y := by simp [z]
    refine ⟨⟨(x, z), Finset.mem_product.mpr ⟨hxS, hz⟩, ?_⟩, hyS⟩
    simp [hsum]


end Sharpness
end StatMech
