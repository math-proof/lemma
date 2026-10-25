/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareGridConsistency.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.Analysis.Calculus.Taylor
import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareGridConsistency.Part4


namespace StatMech.Universality

open Set

noncomputable section

theorem complexDirectionalFourNeighborStencil_le
    (f : Complex → Real) (z v₁ v₂ : Complex) (h M₁ M₂ : Real)
    (hg₁ : ContDiff Real 4
      (fun t : Real ↦ f (z + (t : Complex) * v₁)))
    (hg₂ : ContDiff Real 4
      (fun t : Real ↦ f (z + (t : Complex) * v₂)))
    (hfourth₁ : ∀ t, |iteratedDeriv 4
      (fun s : Real ↦ f (z + (s : Complex) * v₁)) t| ≤ M₁)
    (hfourth₂ : ∀ t, |iteratedDeriv 4
      (fun s : Real ↦ f (z + (s : Complex) * v₂)) t| ≤ M₂)
    (hharmonic : iteratedDeriv 2
        (fun t : Real ↦ f (z + (t : Complex) * v₁)) 0 +
      iteratedDeriv 2
        (fun t : Real ↦ f (z + (t : Complex) * v₂)) 0 = 0) :
    |complexDirectionalFourNeighborStencil f z v₁ v₂ h| ≤
      (M₁ + M₂) * |h| ^ 4 / 12 := by
  rw [show complexDirectionalFourNeighborStencil f z v₁ v₂ h =
      directionalFourNeighborStencil
        (fun t : Real ↦ f (z + (t : Complex) * v₁))
        (fun t : Real ↦ f (z + (t : Complex) * v₂)) h by
    unfold complexDirectionalFourNeighborStencil
      directionalFourNeighborStencil
    push_cast
    simp only [add_zero, zero_mul, sub_eq_add_neg]
    ring]
  exact harmonicDirectionalFourNeighborStencil_le
    (fun t : Real ↦ f (z + (t : Complex) * v₁))
    (fun t : Real ↦ f (z + (t : Complex) * v₂))
    h M₁ M₂ hg₁ hg₂ hfourth₁ hfourth₂ hharmonic

end
end StatMech.Universality
