/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/Kingman.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
open MeasureTheory Filter Topology


namespace StatMech

namespace Kingman

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}


theorem integral_comp_measurePreserving (T : α → α) (hT : MeasurePreserving T μ μ)
    (g : α → ℝ) (hg : AEStronglyMeasurable g μ) :
    ∫ x, g (T x) ∂μ = ∫ x, g x ∂μ := by
  rw [← hT.map_eq] at hg ⊢
  rw [integral_map hT.aemeasurable hg, hT.map_eq]


theorem integral_comp_iterate (T : α → α) (hT : MeasurePreserving T μ μ)
    (g : α → ℝ) (hg : AEStronglyMeasurable g μ) (m : ℕ) :
    ∫ x, g (T^[m] x) ∂μ = ∫ x, g x ∂μ := by
  rw [← (hT.iterate m).map_eq] at hg ⊢
  rw [integral_map (hT.iterate m).aemeasurable hg, (hT.iterate m).map_eq]


end Kingman
end StatMech
