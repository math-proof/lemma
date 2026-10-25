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
import Def.StatisticalMechanics.Code.FrontierA.IsingCriticalOddPrismLayerCoordinates.Part24


namespace StatMech.FrontierA

open StatMech StatMech.Ising StatMech.Sharpness

open Matrix

open scoped BigOperators

noncomputable section

@[simp] theorem oddPrismFlipLayerPath_apply
    {m n k : Nat} (q : Fin k -> RectangularLayerConfig m n) (j : Fin k) :
    oddPrismFlipLayerPath q j = FieldGhostDict.flipV (q j) := rfl

@[simp] theorem oddPrismFlipLayerPath_involutive
    {m n k : Nat} (q : Fin k -> RectangularLayerConfig m n) :
    oddPrismFlipLayerPath (oddPrismFlipLayerPath q) = q := by
  funext j
  exact FieldGhostDict.flipV_involutive (q j)


theorem transferTailPathWeight_flip_cross
    {E : Type*} [Fintype E] [DistribLattice E]
    (flip : E -> E) (A : Matrix E E Real) (a : E -> Real)
    (ha0 : 0 <= a) (hA0 : ∀ x y, 0 <= A x y)
    (ha : ∀ x y,
      a (flip x) * a y <= a (flip (x ⊓ y)) * a (x ⊔ y))
    (hA : ∀ x y u v,
      A (flip x) (flip u) * A y v <=
        A (flip (x ⊓ y)) (flip (u ⊓ v)) * A (x ⊔ y) (u ⊔ v))
    (k : Nat) (q r : Fin (k + 1) -> E) :
    transferTailPathWeight A a k (fun j => flip (q j)) *
        transferTailPathWeight A a k r <=
      transferTailPathWeight A a k (fun j => flip ((q ⊓ r) j)) *
        transferTailPathWeight A a k (q ⊔ r) := by
  have hp :
      (∏ j : Fin k, A (flip (q j.castSucc)) (flip (q j.succ))) *
          (∏ j : Fin k, A (r j.castSucc) (r j.succ)) <=
        (∏ j : Fin k,
          A (flip ((q ⊓ r) j.castSucc)) (flip ((q ⊓ r) j.succ))) *
          ∏ j : Fin k, A ((q ⊔ r) j.castSucc) ((q ⊔ r) j.succ) := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    apply Finset.prod_le_prod
    · intro j _
      exact mul_nonneg (hA0 _ _) (hA0 _ _)
    · intro j _
      simpa only [Pi.inf_apply, Pi.sup_apply] using
        hA (q j.castSucc) (r j.castSucc) (q j.succ) (r j.succ)
  unfold transferTailPathWeight
  calc
    (a (flip (q 0)) *
          ∏ j : Fin k, A (flip (q j.castSucc)) (flip (q j.succ))) *
        (a (r 0) * ∏ j : Fin k, A (r j.castSucc) (r j.succ)) =
      (a (flip (q 0)) * a (r 0)) *
        ((∏ j : Fin k, A (flip (q j.castSucc)) (flip (q j.succ))) *
          ∏ j : Fin k, A (r j.castSucc) (r j.succ)) := by ring
    _ <=
      (a (flip ((q ⊓ r) 0)) * a ((q ⊔ r) 0)) *
        ((∏ j : Fin k,
          A (flip ((q ⊓ r) j.castSucc)) (flip ((q ⊓ r) j.succ))) *
          ∏ j : Fin k, A ((q ⊔ r) j.castSucc) ((q ⊔ r) j.succ)) := by
      apply mul_le_mul
      · simpa only [Pi.inf_apply, Pi.sup_apply] using ha (q 0) (r 0)
      · exact hp
      · exact mul_nonneg
          (Finset.prod_nonneg fun j _ => hA0 _ _)
          (Finset.prod_nonneg fun j _ => hA0 _ _)
      · exact mul_nonneg (ha0 _) (ha0 _)
    _ =
      (a (flip ((q ⊓ r) 0)) *
          ∏ j : Fin k,
            A (flip ((q ⊓ r) j.castSucc)) (flip ((q ⊓ r) j.succ))) *
        (a ((q ⊔ r) 0) *
          ∏ j : Fin k, A ((q ⊔ r) j.castSucc) ((q ⊔ r) j.succ)) := by ring

theorem oddPrismUpperSlabPathWeight_flip_cross
    {beta : Real} (hbeta : 0 <= beta) (n k : Nat)
    (q r : Fin (k + 1) ->
      RectangularLayerConfig (2 * n + 1) (2 * n + 1)) :
    oddPrismUpperSlabPathWeight beta n k (oddPrismFlipLayerPath q) *
        oddPrismUpperSlabPathWeight beta n k r <=
      oddPrismUpperSlabPathWeight beta n k
          (oddPrismFlipLayerPath (q ⊓ r)) *
        oddPrismUpperSlabPathWeight beta n k (q ⊔ r) := by
  let A := rectangularPrismTransfer 1 beta (2 * n + 1) (2 * n + 1)
  let a := rectangularPrismTransferBoundaryVector
    1 beta (2 * n + 1) (2 * n + 1)
  have ha0 : 0 <= a := fun s =>
    (rectangularPrismTransferBoundaryVector_pos
      1 beta (2 * n + 1) (2 * n + 1) s).le
  have hA0 : ∀ s t, 0 <= A s t := fun s t =>
    (rectangularPrismTransfer_pos
      1 beta (2 * n + 1) (2 * n + 1) s t).le
  have htail := transferTailPathWeight_flip_cross
    FieldGhostDict.flipV A a ha0 hA0
      (rectangularPrismTransferBoundaryVector_flip_cross hbeta n)
      (rectangularPrismTransfer_flip_cross hbeta n) k q r
  have hend := oddPrismLayerHalfWeight_flip_cross hbeta n
    (q (Fin.last k)) (r (Fin.last k))
  have htail0 (p : Fin (k + 1) ->
      RectangularLayerConfig (2 * n + 1) (2 * n + 1)) :
      0 <= transferTailPathWeight A a k p := by
    unfold transferTailPathWeight
    exact mul_nonneg (ha0 _) (Finset.prod_nonneg fun j _ => hA0 _ _)
  unfold oddPrismUpperSlabPathWeight
  change (transferTailPathWeight A a k (oddPrismFlipLayerPath q) *
      oddPrismLayerHalfWeight beta n
        (oddPrismFlipLayerPath q (Fin.last k))) *
    (transferTailPathWeight A a k r *
      oddPrismLayerHalfWeight beta n (r (Fin.last k))) <= _
  calc
    (transferTailPathWeight A a k (oddPrismFlipLayerPath q) *
          oddPrismLayerHalfWeight beta n
            (oddPrismFlipLayerPath q (Fin.last k))) *
        (transferTailPathWeight A a k r *
          oddPrismLayerHalfWeight beta n (r (Fin.last k))) =
      (transferTailPathWeight A a k (oddPrismFlipLayerPath q) *
          transferTailPathWeight A a k r) *
        (oddPrismLayerHalfWeight beta n (FieldGhostDict.flipV (q (Fin.last k))) *
          oddPrismLayerHalfWeight beta n (r (Fin.last k))) := by
            simp only [oddPrismFlipLayerPath_apply]
            ring
    _ <=
      (transferTailPathWeight A a k (oddPrismFlipLayerPath (q ⊓ r)) *
          transferTailPathWeight A a k (q ⊔ r)) *
        (oddPrismLayerHalfWeight beta n
            (FieldGhostDict.flipV ((q ⊓ r) (Fin.last k))) *
          oddPrismLayerHalfWeight beta n ((q ⊔ r) (Fin.last k))) := by
      apply mul_le_mul htail
      · simpa only [Pi.inf_apply, Pi.sup_apply] using hend
      · exact mul_nonneg
          (oddPrismLayerHalfWeight_pos beta n _).le
          (oddPrismLayerHalfWeight_pos beta n _).le
      · exact mul_nonneg
          (htail0 (oddPrismFlipLayerPath (q ⊓ r))) (htail0 (q ⊔ r))
    _ =
      (transferTailPathWeight A a k (oddPrismFlipLayerPath (q ⊓ r)) *
          oddPrismLayerHalfWeight beta n
            (oddPrismFlipLayerPath (q ⊓ r) (Fin.last k))) *
        (transferTailPathWeight A a k (q ⊔ r) *
          oddPrismLayerHalfWeight beta n ((q ⊔ r) (Fin.last k))) := by
            simp only [oddPrismFlipLayerPath_apply]
            ring


end
end StatMech.FrontierA
