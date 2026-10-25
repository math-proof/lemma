/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWSpectral.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Mathlib.Analysis.Matrix.Normed
import Theorem.StatisticalMechanics.Code.Onsager.DetWalkExp
import Theorem.StatisticalMechanics.Code.Onsager.KWSpinFourier.Part3
import Def.StatisticalMechanics.Code.Onsager.KWSpectral


namespace StatMech.Onsager

theorem ons_KWconvergenceRadius_pos (L : ℕ) [NeZero L] :
    0 < ons_KWconvergenceRadius L := by
  unfold ons_KWconvergenceRadius
  positivity

theorem ons_KWmatPhase_spectral_small (L : ℕ) [NeZero L]
    {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) (ons_KWconvergenceRadius L)) (a b : Fin 2) :
    ∀ alpha ∈ (ons_KWmatPhase L (x : ℂ) ons_turnRoot
      (ons_spinPhase L a) (ons_spinPhase L b)).charpoly.roots,
      ‖alpha‖ < 1 := by
  apply ons_KWmatPhase_spectral_lt_one L x a b
  have hcard : 0 < (Fintype.card (ons_Dart L) : ℝ) := by positivity
  rw [Real.norm_eq_abs, abs_of_pos hx.1]
  have hxlt : x < 1 / (Fintype.card (ons_Dart L) : ℝ) := by
    simpa [ons_KWconvergenceRadius, div_eq_mul_inv] using hx.2
  exact (lt_div_iff₀' hcard).mp hxlt


theorem ons_KWmatPhase_det_eq_walk_exp (L : ℕ) [NeZero L]
    {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) (ons_KWconvergenceRadius L)) (a b : Fin 2) :
    (1 - ons_KWmatPhase L (x : ℂ) ons_turnRoot
      (ons_spinPhase L a) (ons_spinPhase L b)).det =
      Complex.exp (- ∑' n : ℕ,
        (∑ v : Fin (n + 1) → ons_Dart L, ∏ k : Fin (n + 1),
          ons_KWmatPhase L (x : ℂ) ons_turnRoot
            (ons_spinPhase L a) (ons_spinPhase L b) (v k) (v (k + 1))) / (n + 1)) :=
  ons_det_eq_walk_exp _ (ons_KWmatPhase_spectral_small L hx a b)

end StatMech.Onsager
