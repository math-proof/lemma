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
import Def.StatisticalMechanics.Code.FrontierA.IsingCriticalOddPrismLayerCoordinates.Part21


namespace StatMech.FrontierA

open StatMech StatMech.Ising StatMech.Sharpness

open Matrix

open scoped BigOperators

noncomputable section

theorem oddPrismUpperSlabEndpointMarginal_eq_conditioned
    (beta : Real) (n : Nat) :
    oddPrismUpperSlabEndpointMarginal beta n (n - 1) =
      oddPrismUpperConditionedVector beta n := by
  funext s
  unfold oddPrismUpperSlabEndpointMarginal oddPrismUpperSlabPathWeight
    oddPrismUpperConditionedVector oddPrismUpperTransferTail
  simp only [Fin.snoc_last]
  rw [← Finset.sum_mul]
  rw [sum_transferTailPathWeight_fixed_endpoint]
  · ring
  · exact rectangularPrismTransfer_isHermitian
      1 beta (2 * n + 1) (2 * n + 1)


theorem oddPrismUpperSlabPathWeight_logSupermodular
    {beta : Real} (hbeta : 0 <= beta) (n k : Nat)
    (q r : Fin (k + 1) ->
      RectangularLayerConfig (2 * n + 1) (2 * n + 1)) :
    oddPrismUpperSlabPathWeight beta n k q *
        oddPrismUpperSlabPathWeight beta n k r <=
      oddPrismUpperSlabPathWeight beta n k (q ⊓ r) *
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
  have ha : ∀ s t, a s * a t <= a (s ⊓ t) * a (s ⊔ t) := by
    intro s t
    exact rectangularPrismTransferBoundaryVector_logSupermodular hbeta n s t
  have hA : ∀ s t v w,
      A s v * A t w <= A (s ⊓ t) (v ⊓ w) * A (s ⊔ t) (v ⊔ w) := by
    intro s t v w
    change rectangularPrismTransfer 1 beta (2 * n + 1) (2 * n + 1) s v *
        rectangularPrismTransfer 1 beta (2 * n + 1) (2 * n + 1) t w <=
      rectangularPrismTransfer 1 beta (2 * n + 1) (2 * n + 1)
          (s ⊓ t) (v ⊓ w) *
        rectangularPrismTransfer 1 beta (2 * n + 1) (2 * n + 1)
          (s ⊔ t) (v ⊔ w)
    rw [← oddPrismTiltedSeamTransfer_eq_rectangularTransfer beta n]
    simpa only [mul_comm] using
      (oddPrismTiltedSeamTransfer_pair_logSupermodular
        hbeta hbeta n s t v w)
  have htail := transferTailPathWeight_logSupermodular
    A a ha0 hA0 ha hA k q r
  have hend :
      oddPrismLayerHalfWeight beta n (q (Fin.last k)) *
          oddPrismLayerHalfWeight beta n (r (Fin.last k)) <=
        oddPrismLayerHalfWeight beta n ((q ⊓ r) (Fin.last k)) *
          oddPrismLayerHalfWeight beta n ((q ⊔ r) (Fin.last k)) := by
    simpa only [Pi.inf_apply, Pi.sup_apply, mul_comm] using
      (oddPrismLayerHalfWeight_logSupermodular hbeta n
        (q (Fin.last k)) (r (Fin.last k)))
  have htail0 (p : Fin (k + 1) ->
      RectangularLayerConfig (2 * n + 1) (2 * n + 1)) :
      0 <= transferTailPathWeight A a k p := by
    unfold transferTailPathWeight
    exact mul_nonneg (ha0 _) (Finset.prod_nonneg fun j _ => hA0 _ _)
  unfold oddPrismUpperSlabPathWeight
  change (transferTailPathWeight A a k q *
      oddPrismLayerHalfWeight beta n (q (Fin.last k))) *
    (transferTailPathWeight A a k r *
      oddPrismLayerHalfWeight beta n (r (Fin.last k))) <= _
  calc
    (transferTailPathWeight A a k q *
          oddPrismLayerHalfWeight beta n (q (Fin.last k))) *
        (transferTailPathWeight A a k r *
          oddPrismLayerHalfWeight beta n (r (Fin.last k))) =
      (transferTailPathWeight A a k q * transferTailPathWeight A a k r) *
        (oddPrismLayerHalfWeight beta n (q (Fin.last k)) *
          oddPrismLayerHalfWeight beta n (r (Fin.last k))) := by ring
    _ <=
      (transferTailPathWeight A a k (q ⊓ r) *
          transferTailPathWeight A a k (q ⊔ r)) *
        (oddPrismLayerHalfWeight beta n ((q ⊓ r) (Fin.last k)) *
          oddPrismLayerHalfWeight beta n ((q ⊔ r) (Fin.last k))) := by
      apply mul_le_mul htail hend
      · exact mul_nonneg
          (oddPrismLayerHalfWeight_pos beta n _).le
          (oddPrismLayerHalfWeight_pos beta n _).le
      · exact mul_nonneg (htail0 (q ⊓ r)) (htail0 (q ⊔ r))
    _ =
      (transferTailPathWeight A a k (q ⊓ r) *
          oddPrismLayerHalfWeight beta n ((q ⊓ r) (Fin.last k))) *
        (transferTailPathWeight A a k (q ⊔ r) *
          oddPrismLayerHalfWeight beta n ((q ⊔ r) (Fin.last k))) := by ring


theorem oddPrismUpperSlabEndpointMarginal_logSupermodular
    {beta : Real} (hbeta : 0 <= beta) (n k : Nat)
    (s t : RectangularLayerConfig (2 * n + 1) (2 * n + 1)) :
    oddPrismUpperSlabEndpointMarginal beta n k s *
        oddPrismUpperSlabEndpointMarginal beta n k t <=
      oddPrismUpperSlabEndpointMarginal beta n k (s ⊓ t) *
        oddPrismUpperSlabEndpointMarginal beta n k (s ⊔ t) := by
  let F : (RectangularLayerConfig (2 * n + 1) (2 * n + 1) ×
      (Fin k -> RectangularLayerConfig (2 * n + 1) (2 * n + 1))) -> Real :=
    fun p => oddPrismUpperSlabPathWeight beta n k (Fin.snoc p.2 p.1)
  have hF : 0 <= F := by
    intro p
    unfold F oddPrismUpperSlabPathWeight transferTailPathWeight
    exact mul_nonneg
      (mul_nonneg
        (rectangularPrismTransferBoundaryVector_pos
          1 beta (2 * n + 1) (2 * n + 1) _).le
        (Finset.prod_nonneg fun j _ =>
          (rectangularPrismTransfer_pos
            1 beta (2 * n + 1) (2 * n + 1) _ _).le))
      (oddPrismLayerHalfWeight_pos beta n _).le
  have hlog : ∀ x y, F x * F y <= F (x ⊓ y) * F (x ⊔ y) := by
    intro x y
    obtain ⟨s, q⟩ := x
    obtain ⟨t, r⟩ := y
    have hpath := oddPrismUpperSlabPathWeight_logSupermodular
      hbeta n k (Fin.snoc q s) (Fin.snoc r t)
    have hinf : Fin.snoc q s ⊓ Fin.snoc r t =
        @Fin.snoc k
          (fun _ : Fin (k + 1) =>
            RectangularLayerConfig (2 * n + 1) (2 * n + 1))
          (q ⊓ r) (s ⊓ t) := by
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp
      · simp
    have hsup : Fin.snoc q s ⊔ Fin.snoc r t =
        @Fin.snoc k
          (fun _ : Fin (k + 1) =>
            RectangularLayerConfig (2 * n + 1) (2 * n + 1))
          (q ⊔ r) (s ⊔ t) := by
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp
      · simp
    rw [hinf, hsup] at hpath
    exact hpath
  exact finiteMarginal_logSupermodular F hF hlog s t


theorem oddPrismUpperConditionedVector_logSupermodular
    {beta : Real} (hbeta : 0 <= beta) (n : Nat)
    (s t : RectangularLayerConfig (2 * n + 1) (2 * n + 1)) :
    oddPrismUpperConditionedVector beta n s *
        oddPrismUpperConditionedVector beta n t <=
      oddPrismUpperConditionedVector beta n (s ⊓ t) *
        oddPrismUpperConditionedVector beta n (s ⊔ t) := by
  rw [← oddPrismUpperSlabEndpointMarginal_eq_conditioned beta n]
  exact oddPrismUpperSlabEndpointMarginal_logSupermodular hbeta n (n - 1) s t


end
end StatMech.FrontierA
