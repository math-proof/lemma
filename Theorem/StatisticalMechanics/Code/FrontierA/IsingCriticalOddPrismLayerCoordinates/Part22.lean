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
import Def.StatisticalMechanics.Code.FrontierA.IsingCriticalOddPrismLayerCoordinates.Part22


namespace StatMech.FrontierA

open StatMech StatMech.Ising StatMech.Sharpness

open Matrix

open scoped BigOperators

noncomputable section

theorem oddPrismUpperOneStepMarginal_logSupermodular
    {beta : Real} (hbeta : 0 <= beta) (n : Nat)
    (s t : RectangularLayerConfig (2 * n + 1) (2 * n + 1)) :
    oddPrismUpperOneStepMarginal beta n s *
        oddPrismUpperOneStepMarginal beta n t <=
      oddPrismUpperOneStepMarginal beta n (s ⊓ t) *
        oddPrismUpperOneStepMarginal beta n (s ⊔ t) := by
  let F : (RectangularLayerConfig (2 * n + 1) (2 * n + 1) ×
      RectangularLayerConfig (2 * n + 1) (2 * n + 1)) -> Real :=
    fun p => oddPrismPureSeamKernel beta n p.1 p.2 *
      oddPrismUpperConditionedVector beta n p.2
  have hF : 0 <= F := by
    intro p
    exact mul_nonneg (oddPrismPureSeamKernel_pos beta n _ _).le
      (oddPrismUpperConditionedVector_pos beta n _).le
  have hlog : ∀ x y, F x * F y <= F (x ⊓ y) * F (x ⊔ y) := by
    intro x y
    obtain ⟨s, v⟩ := x
    obtain ⟨t, w⟩ := y
    have hk := oddPrismPureSeamKernel_pair_logSupermodular
      hbeta n s t v w
    have hu := oddPrismUpperConditionedVector_logSupermodular
      hbeta n v w
    have hk0 (a b : RectangularLayerConfig (2 * n + 1) (2 * n + 1)) :
        0 <= oddPrismPureSeamKernel beta n a b :=
      (oddPrismPureSeamKernel_pos beta n a b).le
    have hu0 (a : RectangularLayerConfig (2 * n + 1) (2 * n + 1)) :
        0 <= oddPrismUpperConditionedVector beta n a :=
      (oddPrismUpperConditionedVector_pos beta n a).le
    unfold F
    calc
      (oddPrismPureSeamKernel beta n s v *
          oddPrismUpperConditionedVector beta n v) *
        (oddPrismPureSeamKernel beta n t w *
          oddPrismUpperConditionedVector beta n w) =
        (oddPrismPureSeamKernel beta n s v *
          oddPrismPureSeamKernel beta n t w) *
        (oddPrismUpperConditionedVector beta n v *
          oddPrismUpperConditionedVector beta n w) := by ring
      _ <=
        (oddPrismPureSeamKernel beta n (s ⊓ t) (v ⊓ w) *
          oddPrismPureSeamKernel beta n (s ⊔ t) (v ⊔ w)) *
        (oddPrismUpperConditionedVector beta n (v ⊓ w) *
          oddPrismUpperConditionedVector beta n (v ⊔ w)) := by
        apply mul_le_mul
        · simpa only [mul_comm] using hk
        · exact hu
        · exact mul_nonneg (hu0 v) (hu0 w)
        · exact mul_nonneg
            (hk0 (s ⊓ t) (v ⊓ w)) (hk0 (s ⊔ t) (v ⊔ w))
      _ =
        (oddPrismPureSeamKernel beta n (s ⊓ t) (v ⊓ w) *
          oddPrismUpperConditionedVector beta n (v ⊓ w)) *
        (oddPrismPureSeamKernel beta n (s ⊔ t) (v ⊔ w) *
          oddPrismUpperConditionedVector beta n (v ⊔ w)) := by ring
  exact finiteMarginal_logSupermodular F hF hlog s t


theorem oddPrismLowerConditionedVector_logSupermodular
    {beta : Real} (hbeta : 0 <= beta) (n : Nat) (hn : 0 < n)
    (s t : RectangularLayerConfig (2 * n + 1) (2 * n + 1)) :
    oddPrismLowerConditionedVector beta n s *
        oddPrismLowerConditionedVector beta n t <=
      oddPrismLowerConditionedVector beta n (s ⊓ t) *
        oddPrismLowerConditionedVector beta n (s ⊔ t) := by
  rw [oddPrismLowerConditionedVector_eq_threeLayerEndpoint beta n hn s,
    oddPrismLowerConditionedVector_eq_threeLayerEndpoint beta n hn t,
    oddPrismLowerConditionedVector_eq_threeLayerEndpoint beta n hn (s ⊓ t),
    oddPrismLowerConditionedVector_eq_threeLayerEndpoint beta n hn (s ⊔ t)]
  change (oddPrismLayerHalfWeight beta n s ^ 2 *
      oddPrismUpperOneStepMarginal beta n s) *
    (oddPrismLayerHalfWeight beta n t ^ 2 *
      oddPrismUpperOneStepMarginal beta n t) <= _
  have hh := oddPrismLayerHalfWeight_logSupermodular hbeta n s t
  have hh2 :
      oddPrismLayerHalfWeight beta n s ^ 2 *
          oddPrismLayerHalfWeight beta n t ^ 2 <=
        oddPrismLayerHalfWeight beta n (s ⊓ t) ^ 2 *
          oddPrismLayerHalfWeight beta n (s ⊔ t) ^ 2 := by
    have h0 : 0 <= oddPrismLayerHalfWeight beta n s *
        oddPrismLayerHalfWeight beta n t := mul_nonneg
      (oddPrismLayerHalfWeight_pos beta n s).le
      (oddPrismLayerHalfWeight_pos beta n t).le
    have h1 : 0 <= oddPrismLayerHalfWeight beta n (s ⊓ t) *
        oddPrismLayerHalfWeight beta n (s ⊔ t) := mul_nonneg
      (oddPrismLayerHalfWeight_pos beta n _).le
      (oddPrismLayerHalfWeight_pos beta n _).le
    nlinarith
  have hm := oddPrismUpperOneStepMarginal_logSupermodular hbeta n s t
  have hm0 (u : RectangularLayerConfig (2 * n + 1) (2 * n + 1)) :
      0 <= oddPrismUpperOneStepMarginal beta n u := by
    unfold oddPrismUpperOneStepMarginal
    exact Finset.sum_nonneg fun v _ => mul_nonneg
      (oddPrismPureSeamKernel_pos beta n u v).le
      (oddPrismUpperConditionedVector_pos beta n v).le
  calc
    (oddPrismLayerHalfWeight beta n s ^ 2 *
          oddPrismUpperOneStepMarginal beta n s) *
        (oddPrismLayerHalfWeight beta n t ^ 2 *
          oddPrismUpperOneStepMarginal beta n t) =
      (oddPrismLayerHalfWeight beta n s ^ 2 *
          oddPrismLayerHalfWeight beta n t ^ 2) *
        (oddPrismUpperOneStepMarginal beta n s *
          oddPrismUpperOneStepMarginal beta n t) := by ring
    _ <=
      (oddPrismLayerHalfWeight beta n (s ⊓ t) ^ 2 *
          oddPrismLayerHalfWeight beta n (s ⊔ t) ^ 2) *
        (oddPrismUpperOneStepMarginal beta n (s ⊓ t) *
          oddPrismUpperOneStepMarginal beta n (s ⊔ t)) := by
      apply mul_le_mul hh2 hm
      · exact mul_nonneg (hm0 s) (hm0 t)
      · positivity
    _ =
      (oddPrismLayerHalfWeight beta n (s ⊓ t) ^ 2 *
          oddPrismUpperOneStepMarginal beta n (s ⊓ t)) *
        (oddPrismLayerHalfWeight beta n (s ⊔ t) ^ 2 *
          oddPrismUpperOneStepMarginal beta n (s ⊔ t)) := by ring


theorem oddPrismTransferPairBaseWeight_logSupermodular
    {beta : Real} (hbeta : 0 <= beta) (n : Nat) (hn : 0 < n)
    (x y : RectangularLayerConfig (2 * n + 1) (2 * n + 1) ×
      RectangularLayerConfig (2 * n + 1) (2 * n + 1)) :
    oddPrismTransferPairBaseWeight beta n x *
        oddPrismTransferPairBaseWeight beta n y <=
      oddPrismTransferPairBaseWeight beta n (x ⊓ y) *
        oddPrismTransferPairBaseWeight beta n (x ⊔ y) := by
  obtain ⟨s, v⟩ := x
  obtain ⟨t, w⟩ := y
  have hl := oddPrismLowerConditionedVector_logSupermodular
    hbeta n hn s t
  have hu := oddPrismUpperConditionedVector_logSupermodular
    hbeta n v w
  have hl0 (u : RectangularLayerConfig (2 * n + 1) (2 * n + 1)) :
      0 <= oddPrismLowerConditionedVector beta n u := by
    unfold oddPrismLowerConditionedVector
    exact mul_nonneg (oddPrismLayerHalfWeight_pos beta n u).le
      (rectangularPrismTransfer_pow_mulVec_boundary_pos beta n n u).le
  have hu0 (u : RectangularLayerConfig (2 * n + 1) (2 * n + 1)) :
      0 <= oddPrismUpperConditionedVector beta n u :=
    (oddPrismUpperConditionedVector_pos beta n u).le
  unfold oddPrismTransferPairBaseWeight
  calc
    (oddPrismLowerConditionedVector beta n s *
          oddPrismUpperConditionedVector beta n v) *
        (oddPrismLowerConditionedVector beta n t *
          oddPrismUpperConditionedVector beta n w) =
      (oddPrismLowerConditionedVector beta n s *
          oddPrismLowerConditionedVector beta n t) *
        (oddPrismUpperConditionedVector beta n v *
          oddPrismUpperConditionedVector beta n w) := by ring
    _ <=
      (oddPrismLowerConditionedVector beta n (s ⊓ t) *
          oddPrismLowerConditionedVector beta n (s ⊔ t)) *
        (oddPrismUpperConditionedVector beta n (v ⊓ w) *
          oddPrismUpperConditionedVector beta n (v ⊔ w)) := by
      apply mul_le_mul hl hu
      · exact mul_nonneg (hu0 v) (hu0 w)
      · exact mul_nonneg (hl0 (s ⊓ t)) (hl0 (s ⊔ t))
    _ =
      (oddPrismLowerConditionedVector beta n (s ⊓ t) *
          oddPrismUpperConditionedVector beta n (v ⊓ w)) *
        (oddPrismLowerConditionedVector beta n (s ⊔ t) *
          oddPrismUpperConditionedVector beta n (v ⊔ w)) := by ring

theorem oddPrismLowerConditionedVector_pos
    (beta : Real) (n : Nat)
    (s : RectangularLayerConfig (2 * n + 1) (2 * n + 1)) :
    0 < oddPrismLowerConditionedVector beta n s := by
  unfold oddPrismLowerConditionedVector oddPrismLowerTransferTail
  exact mul_pos (oddPrismLayerHalfWeight_pos beta n s)
    (rectangularPrismTransfer_pow_mulVec_boundary_pos beta n n s)

theorem oddPrismTransferPairBaseWeight_pos
    (beta : Real) (n : Nat)
    (x : RectangularLayerConfig (2 * n + 1) (2 * n + 1) ×
      RectangularLayerConfig (2 * n + 1) (2 * n + 1)) :
    0 < oddPrismTransferPairBaseWeight beta n x := by
  exact mul_pos (oddPrismLowerConditionedVector_pos beta n x.1)
    (oddPrismUpperConditionedVector_pos beta n x.2)


end
end StatMech.FrontierA
