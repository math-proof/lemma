/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SpinCoefficientTarget.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.SpinCharacter.Part2
import Theorem.StatisticalMechanics.Code.Onsager.SpinPolynomial.Part4


namespace StatMech.Onsager

open Matrix BigOperators

theorem ons_KWmatPhase_det_eq_spinDetX (L : ℕ) [NeZero L] [Fact (1 < L)]
    (x : ℝ) (a b : Fin 2) :
    (1 - ons_KWmatPhase L (x : ℂ) ons_turnRoot
      (ons_spinPhase L a) (ons_spinPhase L b)).det =
        (ons_spinDetX L x a b : ℂ) := by
  rw [ons_KWmatPhase_det_eq_prod L (x : ℂ) ons_turnRoot
    (ons_spinPhase L a) (ons_spinPhase L b) (ons_spaceRoot L)
    ons_turnRoot_sq (ons_spaceRoot_primitive L (NeZero.ne L))
    (ons_spinPhase_ne_zero L a) (ons_spinPhase_ne_zero L b)]
  have hfactor : ∀ i j : ℕ,
      ((1 + (x : ℂ) ^ 2) ^ 2 -
        (x : ℂ) * (1 - (x : ℂ) ^ 2) *
          (ons_spinPhase L a * ons_spaceRoot L ^ i +
            (ons_spinPhase L a * ons_spaceRoot L ^ i)⁻¹ +
            (ons_spinPhase L b * ons_spaceRoot L ^ j +
              (ons_spinPhase L b * ons_spaceRoot L ^ j)⁻¹))) =
        (((1 + x ^ 2) ^ 2 - 2 * x * (1 - x ^ 2) *
          (Real.cos (2 * Real.pi * (i + (a.val : ℝ) / 2) / L) +
            Real.cos (2 * Real.pi * (j + (b.val : ℝ) / 2) / L)) : ℝ) : ℂ) := by
    intro i j
    rw [ons_spinPhase_spaceRoot_cos, ons_spinPhase_spaceRoot_cos]
    norm_cast
    ring
  let F : ℕ → ℕ → ℂ := fun i j =>
    (((1 + x ^ 2) ^ 2 - 2 * x * (1 - x ^ 2) *
      (Real.cos (2 * Real.pi * ((i : ℝ) + (a.val : ℝ) / 2) / L) +
        Real.cos (2 * Real.pi * ((j : ℝ) + (b.val : ℝ) / 2) / L)) : ℝ) : ℂ)
  let G : (ZMod L × ZMod L) → ℂ := fun z =>
    ((1 + (x : ℂ) ^ 2) ^ 2 -
      (x : ℂ) * (1 - (x : ℂ) ^ 2) *
        (ons_spinPhase L a * ons_spaceRoot L ^ z.1.val +
          (ons_spinPhase L a * ons_spaceRoot L ^ z.1.val)⁻¹ +
          (ons_spinPhase L b * ons_spaceRoot L ^ z.2.val +
            (ons_spinPhase L b * ons_spaceRoot L ^ z.2.val)⁻¹)))
  change (∏ z, G z) = _
  calc
    (∏ z, G z) = (∏ z : ZMod L × ZMod L, F z.1.val z.2.val) := by
      apply Finset.prod_congr rfl
      intro z _
      unfold G F
      exact hfactor z.1.val z.2.val
    _ = ∏ i ∈ Finset.range L, ∏ j ∈ Finset.range L, F i j :=
      prod_zmod_prod_eq_prod_range L F
    _ = (ons_spinDetX L x a b : ℂ) := by
      unfold F ons_spinDetX
      norm_cast


end StatMech.Onsager
