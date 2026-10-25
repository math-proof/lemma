/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/AnimalLLNas.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.KingmanFilling.Part2
import Def.StatisticalMechanics.Code.BeffaraDC.AnimalLLNas
open MeasureTheory Filter Topology Finset
open StatMech.Kingman StatMech.KingmanAE StatMech.KingmanFilling


namespace StatMech

namespace BeffaraDC

theorem shiftEnv_iterate (ω : ℤ → ℝ) (m : ℕ) (i : ℤ) : (shiftEnv^[m] ω) i = ω (i + m) := by
  induction m generalizing i with
  | zero => simp
  | succ k ih => rw [Function.iterate_succ_apply', shiftEnv, ih]; push_cast; ring_nf


theorem shiftEnv_eq_piCongrLeft :
    shiftEnv = ⇑(Equiv.piCongrLeft (fun _ : ℤ => ℝ) (Equiv.addRight (-1 : ℤ))) := by
  funext ω b
  rw [show b = (Equiv.addRight (-1 : ℤ)) ((Equiv.addRight (-1 : ℤ)).symm b) from
        ((Equiv.addRight (-1 : ℤ)).apply_symm_apply b).symm,
      Equiv.piCongrLeft_apply_apply]
  simp only [shiftEnv, Equiv.coe_addRight]; ring_nf


theorem shiftEnv_measurePreserving (ρ : Measure ℝ) [IsProbabilityMeasure ρ] :
    MeasurePreserving shiftEnv (Measure.infinitePi (fun _ : ℤ => ρ))
      (Measure.infinitePi (fun _ : ℤ => ρ)) := by
  have hmeas : Measurable shiftEnv := by
    rw [shiftEnv_eq_piCongrLeft]
    exact (MeasurableEquiv.piCongrLeft (fun _ : ℤ => ℝ) (Equiv.addRight (-1 : ℤ))).measurable
  refine ⟨hmeas, ?_⟩
  rw [shiftEnv_eq_piCongrLeft]
  have h := Measure.infinitePi_map_piCongrLeft (μ := fun _ : ℤ => ρ) (Equiv.addRight (-1 : ℤ))
  convert h using 2


end BeffaraDC
end StatMech
