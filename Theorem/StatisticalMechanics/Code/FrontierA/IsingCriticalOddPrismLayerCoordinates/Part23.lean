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
import Def.StatisticalMechanics.Code.FrontierA.IsingCriticalOddPrismLayerCoordinates.Part23


namespace StatMech.FrontierA

open StatMech StatMech.Ising StatMech.Sharpness

open Matrix

open scoped BigOperators

noncomputable section

theorem oddPrismTransferTiltedPairWeight_pos
    (beta : Real) (n : Nat) (r : Real)
    (x : RectangularLayerConfig (2 * n + 1) (2 * n + 1) ×
      RectangularLayerConfig (2 * n + 1) (2 * n + 1)) :
    0 < oddPrismTransferTiltedPairWeight beta n r x := by
  exact mul_pos (oddPrismTransferPairBaseWeight_pos beta n x)
    (oddPrismPureSeamKernel_pos r n x.1 x.2)


theorem oddPrismTransferTiltedPairWeight_logSupermodular
    {beta r : Real} (hbeta : 0 <= beta) (hr : 0 <= r)
    (n : Nat) (hn : 0 < n)
    (x y : RectangularLayerConfig (2 * n + 1) (2 * n + 1) ×
      RectangularLayerConfig (2 * n + 1) (2 * n + 1)) :
    oddPrismTransferTiltedPairWeight beta n r x *
        oddPrismTransferTiltedPairWeight beta n r y <=
      oddPrismTransferTiltedPairWeight beta n r (x ⊓ y) *
        oddPrismTransferTiltedPairWeight beta n r (x ⊔ y) := by
  obtain ⟨s, v⟩ := x
  obtain ⟨t, w⟩ := y
  have hb := oddPrismTransferPairBaseWeight_logSupermodular
    hbeta n hn (s, v) (t, w)
  have hk := oddPrismPureSeamKernel_pair_logSupermodular
    hr n s t v w
  have hb0 (z : RectangularLayerConfig (2 * n + 1) (2 * n + 1) ×
      RectangularLayerConfig (2 * n + 1) (2 * n + 1)) :
      0 <= oddPrismTransferPairBaseWeight beta n z :=
    (oddPrismTransferPairBaseWeight_pos beta n z).le
  have hk0 (a b : RectangularLayerConfig (2 * n + 1) (2 * n + 1)) :
      0 <= oddPrismPureSeamKernel r n a b :=
    (oddPrismPureSeamKernel_pos r n a b).le
  unfold oddPrismTransferTiltedPairWeight
  calc
    (oddPrismTransferPairBaseWeight beta n (s, v) *
          oddPrismPureSeamKernel r n s v) *
        (oddPrismTransferPairBaseWeight beta n (t, w) *
          oddPrismPureSeamKernel r n t w) =
      (oddPrismTransferPairBaseWeight beta n (s, v) *
          oddPrismTransferPairBaseWeight beta n (t, w)) *
        (oddPrismPureSeamKernel r n s v *
          oddPrismPureSeamKernel r n t w) := by ring
    _ <=
      (oddPrismTransferPairBaseWeight beta n ((s, v) ⊓ (t, w)) *
          oddPrismTransferPairBaseWeight beta n ((s, v) ⊔ (t, w))) *
        (oddPrismPureSeamKernel r n (s ⊓ t) (v ⊓ w) *
          oddPrismPureSeamKernel r n (s ⊔ t) (v ⊔ w)) := by
      apply mul_le_mul
      · exact hb
      · simpa only [mul_comm] using hk
      · exact mul_nonneg (hk0 s v) (hk0 t w)
      · exact mul_nonneg (hb0 ((s, v) ⊓ (t, w)))
          (hb0 ((s, v) ⊔ (t, w)))
    _ =
      (oddPrismTransferPairBaseWeight beta n ((s, v) ⊓ (t, w)) *
          oddPrismPureSeamKernel r n (s ⊓ t) (v ⊓ w)) *
        (oddPrismTransferPairBaseWeight beta n ((s, v) ⊔ (t, w)) *
          oddPrismPureSeamKernel r n (s ⊔ t) (v ⊔ w)) := by ring

theorem oddPrismTransferBridgeRawMoment_eq_sum_tiltedPairWeight
    (beta : Real) (n : Nat) (r : Real) :
    oddPrismTransferBridgeRawMoment beta n r =
      ∑ x, oddPrismTransferTiltedPairWeight beta n r x := by
  unfold oddPrismTransferBridgeRawMoment oddPrismTransferTiltedPairWeight
    oddPrismTransferPairBaseWeight
  rw [Fintype.sum_prod_type]


@[simp] theorem flipV_inf {V : Type*} (s t : ConfigSpace V) :
    FieldGhostDict.flipV (s ⊓ t) =
      FieldGhostDict.flipV s ⊔ FieldGhostDict.flipV t := by
  funext p
  by_cases hs : s p <;> by_cases ht : t p <;>
    simp [FieldGhostDict.flipV, hs, ht]

@[simp] theorem flipV_sup {V : Type*} (s t : ConfigSpace V) :
    FieldGhostDict.flipV (s ⊔ t) =
      FieldGhostDict.flipV s ⊓ FieldGhostDict.flipV t := by
  funext p
  by_cases hs : s p <;> by_cases ht : t p <;>
    simp [FieldGhostDict.flipV, hs, ht]

theorem rectangularLayerInternalInteraction_flip
    {m n : Nat} (s : RectangularLayerConfig m n) :
    rectangularLayerInternalInteraction (FieldGhostDict.flipV s) =
      rectangularLayerInternalInteraction s := by
  unfold rectangularLayerInternalInteraction
  simp_rw [FieldGhostDict.spin_flipV]
  ring

theorem spin_neg_add_le_inf_sup
    {V : Type*} (s t : ConfigSpace V) (p : V) :
    -spin s p + spin t p <= -spin (s ⊓ t) p + spin (s ⊔ t) p := by
  by_cases hs : s p <;> by_cases ht : t p <;>
    simp [spin, hs, ht] <;> norm_num

theorem rectangularLayerBoundaryInteraction_flip
    {m n : Nat} (s : RectangularLayerConfig m n) :
    (∑ p : Fin m × Fin n,
      rectangularLayerBoundaryDegree p * spin (FieldGhostDict.flipV s) p) =
      -∑ p : Fin m × Fin n,
        rectangularLayerBoundaryDegree p * spin s p := by
  simp_rw [FieldGhostDict.spin_flipV, mul_neg]
  rw [Finset.sum_neg_distrib]

theorem rectangularLayerBoundaryInteraction_cross
    {m n : Nat} (s t : RectangularLayerConfig m n) :
    -(∑ p : Fin m × Fin n,
        rectangularLayerBoundaryDegree p * spin s p) +
        ∑ p : Fin m × Fin n,
          rectangularLayerBoundaryDegree p * spin t p <=
      -(∑ p : Fin m × Fin n,
        rectangularLayerBoundaryDegree p * spin (s ⊓ t) p) +
        ∑ p : Fin m × Fin n,
          rectangularLayerBoundaryDegree p * spin (s ⊔ t) p := by
  rw [← Finset.sum_neg_distrib, ← Finset.sum_neg_distrib,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro p _
  have hp := spin_neg_add_le_inf_sup s t p
  have hd : 0 <= (rectangularLayerBoundaryDegree p : Real) := Nat.cast_nonneg _
  nlinarith


theorem rectangularLayerBoltzmannInteraction_flip_cross
    {beta : Real} (hbeta : 0 <= beta) {m n : Nat}
    (s t : RectangularLayerConfig m n) :
    rectangularLayerBoltzmannInteraction 1 beta (FieldGhostDict.flipV s) +
        rectangularLayerBoltzmannInteraction 1 beta t <=
      rectangularLayerBoltzmannInteraction 1 beta
          (FieldGhostDict.flipV (s ⊓ t)) +
        rectangularLayerBoltzmannInteraction 1 beta (s ⊔ t) := by
  have hi := rectangularLayerInternalInteraction_supermodular s t
  have hb := rectangularLayerBoundaryInteraction_cross s t
  unfold rectangularLayerBoltzmannInteraction
  norm_num
  rw [← flipV_inf s t]
  rw [rectangularLayerInternalInteraction_flip,
    rectangularLayerInternalInteraction_flip,
    rectangularLayerBoundaryInteraction_flip,
    rectangularLayerBoundaryInteraction_flip]
  nlinarith [mul_nonneg hbeta (add_nonneg
    (sub_nonneg.mpr hi) (sub_nonneg.mpr hb))]

theorem oddPrismLayerHalfWeight_flip_cross
    {beta : Real} (hbeta : 0 <= beta) (n : Nat)
    (s t : RectangularLayerConfig (2 * n + 1) (2 * n + 1)) :
    oddPrismLayerHalfWeight beta n (FieldGhostDict.flipV s) *
        oddPrismLayerHalfWeight beta n t <=
      oddPrismLayerHalfWeight beta n (FieldGhostDict.flipV (s ⊓ t)) *
        oddPrismLayerHalfWeight beta n (s ⊔ t) := by
  unfold oddPrismLayerHalfWeight
  rw [← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h := rectangularLayerBoltzmannInteraction_flip_cross hbeta s t
  linarith

theorem rectangularLayerFaceBoundary_flip
    (beta : Real) {m n : Nat} (s : RectangularLayerConfig m n) :
    rectangularLayerFaceBoundary 1 beta (FieldGhostDict.flipV s) =
      -rectangularLayerFaceBoundary 1 beta s := by
  unfold rectangularLayerFaceBoundary
  norm_num
  simp_rw [FieldGhostDict.spin_flipV]
  rw [Finset.sum_neg_distrib]
  ring

theorem rectangularLayerFaceBoundary_flip_cross
    {beta : Real} (hbeta : 0 <= beta) {m n : Nat}
    (s t : RectangularLayerConfig m n) :
    rectangularLayerFaceBoundary 1 beta (FieldGhostDict.flipV s) +
        rectangularLayerFaceBoundary 1 beta t <=
      rectangularLayerFaceBoundary 1 beta (FieldGhostDict.flipV (s ⊓ t)) +
        rectangularLayerFaceBoundary 1 beta (s ⊔ t) := by
  have hs :
      -(∑ p : Fin m × Fin n, spin s p) +
          ∑ p : Fin m × Fin n, spin t p <=
        -(∑ p : Fin m × Fin n, spin (s ⊓ t) p) +
          ∑ p : Fin m × Fin n, spin (s ⊔ t) p := by
    rw [← Finset.sum_neg_distrib, ← Finset.sum_neg_distrib,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun p _ => spin_neg_add_le_inf_sup s t p
  rw [rectangularLayerFaceBoundary_flip,
    rectangularLayerFaceBoundary_flip]
  unfold rectangularLayerFaceBoundary
  norm_num
  nlinarith [mul_nonneg hbeta (sub_nonneg.mpr hs)]

theorem rectangularPrismTransferBoundaryVector_flip_cross
    {beta : Real} (hbeta : 0 <= beta) (n : Nat)
    (s t : RectangularLayerConfig (2 * n + 1) (2 * n + 1)) :
    rectangularPrismTransferBoundaryVector 1 beta
          (2 * n + 1) (2 * n + 1) (FieldGhostDict.flipV s) *
        rectangularPrismTransferBoundaryVector 1 beta
          (2 * n + 1) (2 * n + 1) t <=
      rectangularPrismTransferBoundaryVector 1 beta
          (2 * n + 1) (2 * n + 1) (FieldGhostDict.flipV (s ⊓ t)) *
        rectangularPrismTransferBoundaryVector 1 beta
          (2 * n + 1) (2 * n + 1) (s ⊔ t) := by
  unfold rectangularPrismTransferBoundaryVector
  rw [← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hi := rectangularLayerBoltzmannInteraction_flip_cross hbeta s t
  have hf := rectangularLayerFaceBoundary_flip_cross hbeta s t
  linarith

@[simp] theorem oddPrismLayerSeamInteraction_flip_both
    (n : Nat)
    (s t : RectangularLayerConfig (2 * n + 1) (2 * n + 1)) :
    oddPrismLayerSeamInteraction n (FieldGhostDict.flipV s)
        (FieldGhostDict.flipV t) = oddPrismLayerSeamInteraction n s t := by
  unfold oddPrismLayerSeamInteraction
  simp_rw [FieldGhostDict.spin_flipV]
  apply Finset.sum_congr rfl
  intro p _
  ring

@[simp] theorem oddPrismPureSeamKernel_flip_both
    (r : Real) (n : Nat)
    (s t : RectangularLayerConfig (2 * n + 1) (2 * n + 1)) :
    oddPrismPureSeamKernel r n (FieldGhostDict.flipV s)
        (FieldGhostDict.flipV t) = oddPrismPureSeamKernel r n s t := by
  unfold oddPrismPureSeamKernel
  rw [oddPrismLayerSeamInteraction_flip_both]

theorem oddPrismPureSeamKernel_flip_cross
    {r : Real} (hr : 0 <= r) (n : Nat)
    (s t v w : RectangularLayerConfig (2 * n + 1) (2 * n + 1)) :
    oddPrismPureSeamKernel r n (FieldGhostDict.flipV s)
          (FieldGhostDict.flipV v) *
        oddPrismPureSeamKernel r n t w <=
      oddPrismPureSeamKernel r n (FieldGhostDict.flipV (s ⊓ t))
          (FieldGhostDict.flipV (v ⊓ w)) *
        oddPrismPureSeamKernel r n (s ⊔ t) (v ⊔ w) := by
  simp only [oddPrismPureSeamKernel_flip_both]
  simpa only [mul_comm] using
    (oddPrismPureSeamKernel_pair_logSupermodular hr n s t v w)

theorem rectangularPrismTransfer_flip_cross
    {beta : Real} (hbeta : 0 <= beta) (n : Nat)
    (s t v w : RectangularLayerConfig (2 * n + 1) (2 * n + 1)) :
    rectangularPrismTransfer 1 beta (2 * n + 1) (2 * n + 1)
          (FieldGhostDict.flipV s) (FieldGhostDict.flipV v) *
        rectangularPrismTransfer 1 beta (2 * n + 1) (2 * n + 1) t w <=
      rectangularPrismTransfer 1 beta (2 * n + 1) (2 * n + 1)
          (FieldGhostDict.flipV (s ⊓ t)) (FieldGhostDict.flipV (v ⊓ w)) *
        rectangularPrismTransfer 1 beta (2 * n + 1) (2 * n + 1)
          (s ⊔ t) (v ⊔ w) := by
  rw [← oddPrismTiltedSeamTransfer_eq_rectangularTransfer beta n]
  unfold oddPrismTiltedSeamTransfer
  have hs := oddPrismLayerHalfWeight_flip_cross hbeta n s t
  have hv := oddPrismLayerHalfWeight_flip_cross hbeta n v w
  have hk := oddPrismPureSeamKernel_flip_cross hbeta n s t v w
  have hh0 (a : RectangularLayerConfig (2 * n + 1) (2 * n + 1)) :
      0 <= oddPrismLayerHalfWeight beta n a :=
    (oddPrismLayerHalfWeight_pos beta n a).le
  have hk0 (a b : RectangularLayerConfig (2 * n + 1) (2 * n + 1)) :
      0 <= oddPrismPureSeamKernel beta n a b :=
    (oddPrismPureSeamKernel_pos beta n a b).le
  calc
    (oddPrismLayerHalfWeight beta n (FieldGhostDict.flipV s) *
          oddPrismPureSeamKernel beta n (FieldGhostDict.flipV s)
            (FieldGhostDict.flipV v) *
          oddPrismLayerHalfWeight beta n (FieldGhostDict.flipV v)) *
        (oddPrismLayerHalfWeight beta n t *
          oddPrismPureSeamKernel beta n t w *
          oddPrismLayerHalfWeight beta n w) =
      (oddPrismLayerHalfWeight beta n (FieldGhostDict.flipV s) *
          oddPrismLayerHalfWeight beta n t) *
        (oddPrismPureSeamKernel beta n (FieldGhostDict.flipV s)
            (FieldGhostDict.flipV v) * oddPrismPureSeamKernel beta n t w) *
        (oddPrismLayerHalfWeight beta n (FieldGhostDict.flipV v) *
          oddPrismLayerHalfWeight beta n w) := by ring
    _ <=
      (oddPrismLayerHalfWeight beta n (FieldGhostDict.flipV (s ⊓ t)) *
          oddPrismLayerHalfWeight beta n (s ⊔ t)) *
        (oddPrismPureSeamKernel beta n (FieldGhostDict.flipV (s ⊓ t))
            (FieldGhostDict.flipV (v ⊓ w)) *
          oddPrismPureSeamKernel beta n (s ⊔ t) (v ⊔ w)) *
        (oddPrismLayerHalfWeight beta n (FieldGhostDict.flipV (v ⊓ w)) *
          oddPrismLayerHalfWeight beta n (v ⊔ w)) := by
      gcongr
      · exact mul_nonneg (hh0 _) (hh0 _)
      · exact mul_nonneg
          (mul_nonneg (hh0 _) (hh0 _)) (mul_nonneg (hk0 _ _) (hk0 _ _))
      · exact mul_nonneg (hk0 _ _) (hk0 _ _)
      · exact mul_nonneg (hh0 _) (hh0 _)
    _ =
      (oddPrismLayerHalfWeight beta n (FieldGhostDict.flipV (s ⊓ t)) *
          oddPrismPureSeamKernel beta n (FieldGhostDict.flipV (s ⊓ t))
            (FieldGhostDict.flipV (v ⊓ w)) *
          oddPrismLayerHalfWeight beta n (FieldGhostDict.flipV (v ⊓ w))) *
        (oddPrismLayerHalfWeight beta n (s ⊔ t) *
          oddPrismPureSeamKernel beta n (s ⊔ t) (v ⊔ w) *
          oddPrismLayerHalfWeight beta n (v ⊔ w)) := by ring


theorem finiteCrossMarginal
    {A B : Type*} [Fintype A] [Fintype B]
    [DistribLattice A] [DistribLattice B]
    (Fminus Fplus : A × B -> Real)
    (hminus : 0 <= Fminus) (hplus : 0 <= Fplus)
    (hcross : ∀ x y,
      Fminus x * Fplus y <=
        Fminus (x ⊓ y) * Fplus (x ⊔ y))
    (x y : A) :
    (∑ b, Fminus (x, b)) * (∑ b, Fplus (y, b)) <=
      (∑ b, Fminus (x ⊓ y, b)) *
        (∑ b, Fplus (x ⊔ y, b)) := by
  apply four_functions_theorem_univ
  · exact fun b => hminus (x, b)
  · exact fun b => hplus (y, b)
  · exact fun b => hminus (x ⊓ y, b)
  · exact fun b => hplus (x ⊔ y, b)
  · intro b c
    simpa only [Prod.inf_def, Prod.sup_def] using
      (hcross (x, b) (y, c))


end
end StatMech.FrontierA
