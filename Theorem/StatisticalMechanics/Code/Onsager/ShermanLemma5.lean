/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanLemma5.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.ShermanLoop


namespace StatMech.Onsager

open Matrix BigOperators


theorem ons_sum_zero_of_sign_involution {E} [Fintype E] [DecidableEq E] (Λ : Matrix E E ℂ)
    {n : ℕ} [NeZero n] (S : Finset (Fin n → E)) (g : (Fin n → E) → (Fin n → E))
    (hmaps : ∀ v ∈ S, g v ∈ S)
    (hsign : ∀ v ∈ S, ons_loopWeight Λ (g v) = - ons_loopWeight Λ v)
    (hinv : ∀ v ∈ S, g (g v) = v) (hne : ∀ v ∈ S, g v ≠ v) :
    ∑ v ∈ S, ons_loopWeight Λ v = 0 := by
  refine Finset.sum_involution (fun v _ => g v) ?_ ?_ ?_ ?_
  · 
    intro v hv
    rw [hsign v hv, add_neg_cancel]
  · 
    intro v hv _
    exact hne v hv
  · 
    intro v hv
    exact hmaps v hv
  · 
    intro v hv
    exact hinv v hv


end StatMech.Onsager
