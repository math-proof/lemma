/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/AizenmanBarsky.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.Sharpness.AizenmanBarsky.Part2
open Set Real Filter Topology

set_option linter.unusedSectionVars false


namespace StatMech

namespace Sharpness

theorem ab_perco_meanfield_sqrt_physical (M : ℝ → ℝ → ℝ) (J βc : ℝ)
    (hβc : 0 < βc) (hJ : 0 < J)
    (hAB : AizenmanBarskyInequalityPhysical M J)
    (hdiff : ∀ h ∈ Ioi (0 : ℝ),
      DifferentiableAt ℝ (fun t => M βc t) h)
    (hmono : ∀ h ∈ Ioi (0 : ℝ),
      0 ≤ deriv (fun t => M βc t) h)
    (hcont0 : ContinuousWithinAt (fun t => M βc t) (Ici (0 : ℝ)) 0)
    (hmnn : ∀ h, 0 ≤ M βc h) (hm0 : M βc 0 = 0)
    (heq6 : ∀ h ∈ Ioi (0 : ℝ),
      1 - M βc h ≤ βc * deriv (fun b => M b h) βc) :
    ∃ c > 0, ∀ h ∈ Ioc (0 : ℝ) (βc * J / 4),
      c * Real.sqrt h ≤ M βc h := by
  let K := βc * J
  have hK : 0 < K := mul_pos hβc hJ
  have heq12 : ∀ h ∈ Ioi (0 : ℝ),
      1 - M βc h ≤ K * (M βc h * deriv (fun t => M βc t) h) := by
    intro h hh
    calc
      1 - M βc h ≤ βc * deriv (fun b => M b h) βc := heq6 h hh
      _ ≤ βc * (J * (M βc h * deriv (fun t => M βc t) h)) :=
        mul_le_mul_of_nonneg_left (hAB βc hβc.le h hh) hβc.le
      _ = K * (M βc h * deriv (fun t => M βc t) h) := by
        dsimp [K]
        ring
  simpa [K] using ab_field_meanfield_bound_pos K hK (fun h => M βc h)
    hdiff hmono hcont0 hmnn hm0 heq12

end Sharpness
end StatMech
