/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingRectangularDobrushinSpinFlip.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingRectangularDobrushin
import Def.StatisticalMechanics.Code.FrontierA.IsingRectangularDobrushinSpinFlip.Part2
open scoped BigOperators
open Finset


namespace StatMech.Ising

noncomputable section

@[simp] theorem rectangularPrismDisorderSheet_not_mem_x
    {m n h : Nat} (q : Fin (m - 1) × Fin n × Fin (2 * h + 1)) :
    Sum.inl q ∉ rectangularPrismDisorderSheet m n h := by
  simp [rectangularPrismDisorderSheet]

@[simp] theorem rectangularPrismDisorderSheet_not_mem_y
    {m n h : Nat} (q : Fin m × Fin (n - 1) × Fin (2 * h + 1)) :
    Sum.inr (Sum.inl q) ∉ rectangularPrismDisorderSheet m n h := by
  simp [rectangularPrismDisorderSheet]

@[simp] theorem rectangularPrismDisorderSheet_mem_z_iff
    {m n h : Nat} (q : Fin m × Fin n × Fin (2 * h)) :
    Sum.inr (Sum.inr (Sum.inl q)) ∈
        rectangularPrismDisorderSheet m n h <-> q.2.2.val = h := by
  simp [rectangularPrismDisorderSheet]

@[simp] theorem rectangularPrismDisorderSheet_not_mem_boundary
    {m n h : Nat} (v : RectangularPrismSite m n h) :
    Sum.inr (Sum.inr (Sum.inr v)) ∉
      rectangularPrismDisorderSheet m n h := by
  simp [rectangularPrismDisorderSheet]


theorem reverseSheet_mul_monomial_upperHalfFlip
    (J beta : Real) {m n h : Nat}
    (q : RectangularPrismInteraction m n h)
    (sigma : RectangularPrismConfig m n h) :
    reverseInteractionCoupling
          (rectangularPrismInteractionCoupling J beta)
          (rectangularPrismDisorderSheet m n h) q *
        rectangularPrismInteractionMonomial q
          (rectangularPrismUpperHalfFlip sigma) =
      rectangularPrismDobrushinCoupling J beta q *
        rectangularPrismInteractionMonomial q sigma := by
  rcases q with q | q
  · rcases q with ⟨x, y, z⟩
    by_cases hz : h < z.val <;>
      simp [reverseInteractionCoupling,
        rectangularPrismInteractionCoupling,
        rectangularPrismDobrushinCoupling,
        rectangularPrismInteractionMonomial,
        rectangularPrismSpin_upperHalfFlip, hz]
  · rcases q with q | q
    · rcases q with ⟨x, y, z⟩
      by_cases hz : h < z.val <;>
        simp [reverseInteractionCoupling,
          rectangularPrismInteractionCoupling,
          rectangularPrismDobrushinCoupling,
          rectangularPrismInteractionMonomial,
          rectangularPrismSpin_upperHalfFlip, hz]
    · rcases q with q | v
      · rcases q with ⟨x, y, z⟩
        by_cases hz : z.val = h
        · simp [reverseInteractionCoupling,
            rectangularPrismInteractionCoupling,
            rectangularPrismDobrushinCoupling,
            rectangularPrismInteractionMonomial,
            rectangularPrismSpin_upperHalfFlip, hz]
        · by_cases hbelow : z.val < h
          · have hz0 : ¬ h < z.val := by omega
            have hz1 : ¬ h < z.val + 1 := by omega
            simp [reverseInteractionCoupling,
              rectangularPrismInteractionCoupling,
              rectangularPrismDobrushinCoupling,
              rectangularPrismInteractionMonomial,
              rectangularPrismSpin_upperHalfFlip, hz, hz0, hz1]
          · have hz0 : h < z.val := by omega
            have hz1 : h < z.val + 1 := by omega
            simp [reverseInteractionCoupling,
              rectangularPrismInteractionCoupling,
              rectangularPrismDobrushinCoupling,
              rectangularPrismInteractionMonomial,
              rectangularPrismSpin_upperHalfFlip, hz, hz0, hz1]
      · by_cases hz : h < v.z.val
        · by_cases hs : sigma v <;>
            simp [reverseInteractionCoupling,
              rectangularPrismInteractionCoupling,
              rectangularPrismDobrushinCoupling,
              rectangularPrismInteractionMonomial,
              rectangularPrismUpperHalfFlip, spin, hz, hs]
        · by_cases hs : sigma v <;>
            simp [reverseInteractionCoupling,
              rectangularPrismInteractionCoupling,
              rectangularPrismDobrushinCoupling,
              rectangularPrismInteractionMonomial,
              rectangularPrismUpperHalfFlip, spin, hz, hs]


end
end StatMech.Ising
