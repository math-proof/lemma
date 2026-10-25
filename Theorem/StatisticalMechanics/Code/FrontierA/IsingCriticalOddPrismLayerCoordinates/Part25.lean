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
import Def.StatisticalMechanics.Code.FrontierA.IsingCriticalOddPrismLayerCoordinates.Part25


namespace StatMech.FrontierA

open StatMech StatMech.Ising StatMech.Sharpness

open Matrix

open scoped BigOperators

noncomputable section

theorem oddPrismUpperSlabFlippedEndpointMarginal_eq
    (beta : Real) (n k : Nat)
    (s : RectangularLayerConfig (2 * n + 1) (2 * n + 1)) :
    oddPrismUpperSlabFlippedEndpointMarginal beta n k s =
      oddPrismUpperSlabEndpointMarginal beta n k
        (FieldGhostDict.flipV s) := by
  let e : (Fin k -> RectangularLayerConfig (2 * n + 1) (2 * n + 1)) ≃
      (Fin k -> RectangularLayerConfig (2 * n + 1) (2 * n + 1)) :=
    { toFun := oddPrismFlipLayerPath
      invFun := oddPrismFlipLayerPath
      left_inv := oddPrismFlipLayerPath_involutive
      right_inv := oddPrismFlipLayerPath_involutive }
  unfold oddPrismUpperSlabFlippedEndpointMarginal
    oddPrismUpperSlabEndpointMarginal
  calc
    (∑ q : Fin k -> RectangularLayerConfig (2 * n + 1) (2 * n + 1),
      oddPrismUpperSlabPathWeight beta n k
        (oddPrismFlipLayerPath (Fin.snoc q s))) =
      ∑ q : Fin k -> RectangularLayerConfig (2 * n + 1) (2 * n + 1),
        oddPrismUpperSlabPathWeight beta n k
          (Fin.snoc (e q) (FieldGhostDict.flipV s)) := by
      apply Finset.sum_congr rfl
      intro q _
      congr 1
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [e]
      · simp [e]
    _ = _ := Equiv.sum_comp e
      (fun q => oddPrismUpperSlabPathWeight beta n k
        (Fin.snoc q (FieldGhostDict.flipV s)))


theorem oddPrismUpperSlabEndpointMarginal_flip_cross
    {beta : Real} (hbeta : 0 <= beta) (n k : Nat)
    (s t : RectangularLayerConfig (2 * n + 1) (2 * n + 1)) :
    oddPrismUpperSlabFlippedEndpointMarginal beta n k s *
        oddPrismUpperSlabEndpointMarginal beta n k t <=
      oddPrismUpperSlabFlippedEndpointMarginal beta n k (s ⊓ t) *
        oddPrismUpperSlabEndpointMarginal beta n k (s ⊔ t) := by
  let Fminus : (RectangularLayerConfig (2 * n + 1) (2 * n + 1) ×
      (Fin k -> RectangularLayerConfig (2 * n + 1) (2 * n + 1))) -> Real :=
    fun p => oddPrismUpperSlabPathWeight beta n k
      (oddPrismFlipLayerPath (Fin.snoc p.2 p.1))
  let Fplus : (RectangularLayerConfig (2 * n + 1) (2 * n + 1) ×
      (Fin k -> RectangularLayerConfig (2 * n + 1) (2 * n + 1))) -> Real :=
    fun p => oddPrismUpperSlabPathWeight beta n k (Fin.snoc p.2 p.1)
  have hminus : 0 <= Fminus := by
    intro p
    unfold Fminus oddPrismUpperSlabPathWeight transferTailPathWeight
    exact mul_nonneg
      (mul_nonneg
        (rectangularPrismTransferBoundaryVector_pos
          1 beta (2 * n + 1) (2 * n + 1) _).le
        (Finset.prod_nonneg fun j _ =>
          (rectangularPrismTransfer_pos
            1 beta (2 * n + 1) (2 * n + 1) _ _).le))
      (oddPrismLayerHalfWeight_pos beta n _).le
  have hplus : 0 <= Fplus := by
    intro p
    unfold Fplus oddPrismUpperSlabPathWeight transferTailPathWeight
    exact mul_nonneg
      (mul_nonneg
        (rectangularPrismTransferBoundaryVector_pos
          1 beta (2 * n + 1) (2 * n + 1) _).le
        (Finset.prod_nonneg fun j _ =>
          (rectangularPrismTransfer_pos
            1 beta (2 * n + 1) (2 * n + 1) _ _).le))
      (oddPrismLayerHalfWeight_pos beta n _).le
  have hcross : ∀ x y,
      Fminus x * Fplus y <= Fminus (x ⊓ y) * Fplus (x ⊔ y) := by
    intro x y
    obtain ⟨s, q⟩ := x
    obtain ⟨t, r⟩ := y
    have hpath := oddPrismUpperSlabPathWeight_flip_cross
      hbeta n k (Fin.snoc q s) (Fin.snoc r t)
    have hinf : Fin.snoc q s ⊓ Fin.snoc r t =
        @Fin.snoc k
          (fun _ : Fin (k + 1) =>
            RectangularLayerConfig (2 * n + 1) (2 * n + 1))
          (q ⊓ r) (s ⊓ t) := by
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
    have hsup : Fin.snoc q s ⊔ Fin.snoc r t =
        @Fin.snoc k
          (fun _ : Fin (k + 1) =>
            RectangularLayerConfig (2 * n + 1) (2 * n + 1))
          (q ⊔ r) (s ⊔ t) := by
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
    rw [hinf, hsup] at hpath
    exact hpath
  exact finiteCrossMarginal Fminus Fplus hminus hplus hcross s t


theorem oddPrismUpperConditionedVector_flip_cross
    {beta : Real} (hbeta : 0 <= beta) (n : Nat)
    (s t : RectangularLayerConfig (2 * n + 1) (2 * n + 1)) :
    oddPrismUpperConditionedVector beta n (FieldGhostDict.flipV s) *
        oddPrismUpperConditionedVector beta n t <=
      oddPrismUpperConditionedVector beta n (FieldGhostDict.flipV (s ⊓ t)) *
        oddPrismUpperConditionedVector beta n (s ⊔ t) := by
  rw [← oddPrismUpperSlabEndpointMarginal_eq_conditioned beta n]
  rw [← oddPrismUpperSlabFlippedEndpointMarginal_eq beta n (n - 1) s,
    ← oddPrismUpperSlabFlippedEndpointMarginal_eq beta n (n - 1) (s ⊓ t)]
  exact oddPrismUpperSlabEndpointMarginal_flip_cross hbeta n (n - 1) s t


end
end StatMech.FrontierA
