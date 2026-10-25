/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SpinWeightedTarget.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.KWWeightedBounds
import Theorem.StatisticalMechanics.Code.Onsager.KWMultiaffineBounded
import Theorem.StatisticalMechanics.Code.Onsager.SpinCoefficientTarget.Part2
import Def.StatisticalMechanics.Code.Onsager.SpinWeightedTarget.Part2


namespace StatMech.Onsager

open Matrix BigOperators StatMech.Ising

theorem ons_spinCoefficientIdentity_of_weightedRoot
    (L : ℕ) [Fact (2 < L)]
    (hweighted : ons_weightedRootIdentity L)
    {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) (ons_ShermanRadius L)) :
    ons_spinCoefficientIdentity L x := by
  intro a b
  have hbound : ∀ edge : Sym2 (ZMod L × ZMod L),
      ‖(x : ℂ)‖ ≤ x := by
    intro edge
    simp [abs_of_pos hx.1]
  have hroot := hweighted a b (fun _ => (x : ℂ)) x hx.1.le
    hbound (by simpa [ons_ShermanRadius] using hx.2)
  have hsq := ons_KWmatWeightedPhase_detWalkRoot_sq
    L (fun _ => (x : ℂ)) a b x hx.1.le hbound
      (by simpa [ons_ShermanRadius] using hx.2)
  rw [ons_KWmatWeightedPhase_const,
    ons_weightedSpinCharacterSum_const] at hroot
  calc
    (ons_spinCharacterSum L x a b : ℂ) ^ 2 =
        ons_detWalkRoot (ons_KWmatPhase L (x : ℂ) ons_turnRoot
          (ons_spinPhase L a) (ons_spinPhase L b)) ^ 2 := by rw [hroot]
    _ = _ := hsq

end StatMech.Onsager
