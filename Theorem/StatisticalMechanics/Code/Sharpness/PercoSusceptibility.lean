/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/PercoSusceptibility.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BkCriterionInfinite.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.BKFirstExit
import Def.StatisticalMechanics.Code.Sharpness.TildeBc.Part9
import Theorem.StatisticalMechanics.Code.Percolation.DctDifferentialFull.Part2
import Theorem.StatisticalMechanics.Code.Percolation.SubcriticalDecayFull.Part2
import Theorem.StatisticalMechanics.Code.Percolation.SharpnessUnconditional.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanContour.Part3
import Def.StatisticalMechanics.Code.Sharpness.PercoSusceptibility
open MeasureTheory Set Finset Filter
open scoped NNReal ENNReal BigOperators Topology


namespace StatMech

namespace Sharpness

open ConfigSpace SimpleGraph

open StatMech.Lattice StatMech.Percolation

variable {d : ℕ}


@[simp] theorem shk_mem_translateFinset_smul
    (g : Multiplicative (Site d)) (S : Finset (Site d)) (x : Site d) :
    g • x ∈ shk_translateFinset g S ↔ x ∈ S := by
  classical
  constructor
  · intro hx
    rw [shk_translateFinset, Finset.mem_image] at hx
    obtain ⟨y, hy, hxy⟩ := hx
    have : y = x := by
      apply_fun (fun z => g⁻¹ • z) at hxy
      simpa only [inv_smul_smul] using hxy
    simpa [this] using hy
  · intro hx
    exact Finset.mem_image.mpr ⟨x, hx, rfl⟩

theorem shk_translateFinset_card (g : Multiplicative (Site d))
    (S : Finset (Site d)) :
    (shk_translateFinset g S).card = S.card := by
  classical
  exact Finset.card_image_of_injective S
    (MulAction.toPerm (β := Site d) g).injective


end Sharpness
end StatMech
