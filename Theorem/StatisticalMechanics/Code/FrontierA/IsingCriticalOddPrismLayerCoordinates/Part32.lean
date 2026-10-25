/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingCriticalUnequalBridgeGeometry.Part3
import Theorem.StatisticalMechanics.Code.Ising.GHSLebowitz.Part11
import Theorem.StatisticalMechanics.Code.Ising.IsingFKGLayer
import Theorem.StatisticalMechanics.Code.Ising.RectangularPrismTransfer.Part7
import Def.StatisticalMechanics.Code.FrontierA.IsingCriticalOddPrismLayerCoordinates.Part32


namespace StatMech.FrontierA

open StatMech StatMech.Ising StatMech.Sharpness

open Matrix

open scoped BigOperators

noncomputable section

@[simp] theorem ghsLMateEquiv_apply
    {V : Type*} [Fintype V] [DecidableEq V]
    (s q : ConfigSpace V) :
    ghsLMateEquiv s q = ghsLMate q s := rfl


theorem ghsLAgreement_chain
    {V : Type*} (s t v : ConfigSpace V) :
    ghsLAgreement (ghsLAgreement s t) (ghsLAgreement t v) =
      ghsLAgreement s v := by
  funext p
  unfold ghsLAgreement
  cases hs : s p <;> cases ht : t p <;> cases hv : v p <;>
    simp [hs, ht, hv]


theorem oddPrismLayerSeamInteraction_mate_signed
    (n : Nat)
    (c s t : ConfigSpace (Fin (2 * n + 1) × Fin (2 * n + 1))) :
    oddPrismLayerSeamInteraction n s (ghsLMate c t) =
      ∑ p, spin c p * (spin s p * spin t p) := by
  unfold oddPrismLayerSeamInteraction ghsLMate spin
  apply Finset.sum_congr rfl
  intro p _
  by_cases hc : c p <;> cases hs : s p <;> cases ht : t p <;>
    simp [hc, hs, ht]


theorem oddPrism_twoSeamInteraction_eq_endpointAgreementCoupling
    (n : Nat) (a b : Real)
    (c s t : ConfigSpace (Fin (2 * n + 1) × Fin (2 * n + 1))) :
    a * oddPrismLayerSeamInteraction n s (ghsLMate c t) +
        b * oddPrismLayerSeamInteraction n s t =
      ∑ p, (b + a * spin c p) * (spin s p * spin t p) := by
  rw [oddPrismLayerSeamInteraction_mate_signed]
  unfold oddPrismLayerSeamInteraction
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _
  ring

theorem oddPrism_endpointAgreementCoupling_nonneg
    {beta r : Real} (hr : 0 <= r) (hrb : r <= beta)
    {n : Nat}
    (c : ConfigSpace (Fin (2 * n + 1) × Fin (2 * n + 1)))
    (p : Fin (2 * n + 1) × Fin (2 * n + 1)) :
    0 <= beta + r * spin c p := by
  rcases spin_eq_pm c p with hp | hp
  · rw [hp, mul_one]
    linarith
  · rw [hp, mul_neg_one]
    linarith


end
end StatMech.FrontierA
