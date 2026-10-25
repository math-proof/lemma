/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusWindingCountBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusAllChargeReduction
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialLoopVerticalWinding.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialLoopTurningFiber.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectMedialLoopTurnClassification.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectEulerDefectClassification
import Def.StatisticalMechanics.Code.FrontierD.FKRectTorusWindingCountBridge.Part2


namespace StatMech.FrontierD

noncomputable section

theorem fkRectZeroTurnLoopCount_add_nonzeroTurnLoopCount
    (R : FKRectTorus) (omega : R.Configuration) :
    fkRectZeroTurnLoopCount R omega +
        fkRectNonzeroTurnLoopCount R omega =
      fkRectMedialLoopCount R omega := by
  classical
  unfold fkRectZeroTurnLoopCount fkRectNonzeroTurnLoopCount
    fkRectMedialLoopCount fkMedialLoopCount
  rw [Nat.card_eq_fintype_card]
  simpa using (Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (FKMedialLoop R.medialTorus
      (fkRectConfigurationToMedialPairing R omega))))
    (p := fun C => FKMedialTurningFiber.canonicalComponentTurn
      (fkRectConfigurationToMedialPairing R omega) C = 0))


theorem sum_fkRectOrientedLoopWeight_eq_turningProduct
    (R : FKRectTorus) (lam : Real) (omega : R.Configuration) :
    (∑ arrows : SixVertexArrows R.medialTorus,
        fkRectOrientedLoopWeight R lam omega arrows) =
      ∏ C : FKMedialLoop R.medialTorus
          (fkRectConfigurationToMedialPairing R omega),
        (Real.exp ((lam / 4) *
            FKMedialTurningFiber.canonicalComponentTurn
              (fkRectConfigurationToMedialPairing R omega) C) +
          Real.exp (-(lam / 4) *
            FKMedialTurningFiber.canonicalComponentTurn
              (fkRectConfigurationToMedialPairing R omega) C)) := by
  exact FKMedialTurningFiber.sum_orientedLoopWeight_eq_turningProduct
    lam (fkRectConfigurationToMedialPairing R omega)

theorem fkRectTurningProduct_eq_zero_nonzeroTurnPowers
    (R : FKRectTorus) (lam : Real) (omega : R.Configuration) :
    (∏ C : FKMedialLoop R.medialTorus
          (fkRectConfigurationToMedialPairing R omega),
        (Real.exp ((lam / 4) *
            FKMedialTurningFiber.canonicalComponentTurn
              (fkRectConfigurationToMedialPairing R omega) C) +
          Real.exp (-(lam / 4) *
            FKMedialTurningFiber.canonicalComponentTurn
              (fkRectConfigurationToMedialPairing R omega) C))) =
      2 ^ fkRectZeroTurnLoopCount R omega *
        (Real.exp lam + Real.exp (-lam)) ^
          fkRectNonzeroTurnLoopCount R omega := by
  classical
  unfold fkRectZeroTurnLoopCount fkRectNonzeroTurnLoopCount
  rw [← Finset.prod_filter_mul_prod_filter_not
    (s := (Finset.univ : Finset (FKMedialLoop R.medialTorus
      (fkRectConfigurationToMedialPairing R omega))))
    (p := fun C => FKMedialTurningFiber.canonicalComponentTurn
      (fkRectConfigurationToMedialPairing R omega) C = 0)]
  congr 1
  · apply Finset.prod_eq_pow_card
    intro C hC
    apply FKMedialTurningFiber.orientationFactor_eq_two_of_turn_eq_zero
    exact (Finset.mem_filter.mp hC).2
  · apply Finset.prod_eq_pow_card
    intro C hC
    have hne := (Finset.mem_filter.mp hC).2
    have hclass := fkRectCanonicalComponentTurn_classification R
      (fkRectConfigurationToMedialPairing R omega) C
    apply FKMedialTurningFiber.orientationFactor_eq_exp_add_exp_neg_of_turn_eq_four_or_neg_four
    rcases hclass with hzero | hfour | hnegfour
    · exact (hne hzero).elim
    · exact Or.inl hfour
    · exact Or.inr hnegfour

theorem sum_fkRectOrientedLoopWeight_eq_zero_nonzeroTurnPowers
    (R : FKRectTorus) (lam : Real) (omega : R.Configuration) :
    (∑ arrows : SixVertexArrows R.medialTorus,
        fkRectOrientedLoopWeight R lam omega arrows) =
      2 ^ fkRectZeroTurnLoopCount R omega *
        (Real.exp lam + Real.exp (-lam)) ^
          fkRectNonzeroTurnLoopCount R omega := by
  rw [sum_fkRectOrientedLoopWeight_eq_turningProduct,
    fkRectTurningProduct_eq_zero_nonzeroTurnPowers]


theorem fkRectAllOrientedLoopTilt_eq_turningProduct
    (R : FKRectTorus) (q lam : Real) (omega : R.Configuration) :
    fkRectAllOrientedLoopTilt R q lam omega =
      (∏ C : FKMedialLoop R.medialTorus
          (fkRectConfigurationToMedialPairing R omega),
        (Real.exp ((lam / 4) *
            FKMedialTurningFiber.canonicalComponentTurn
              (fkRectConfigurationToMedialPairing R omega) C) +
          Real.exp (-(lam / 4) *
            FKMedialTurningFiber.canonicalComponentTurn
              (fkRectConfigurationToMedialPairing R omega) C))) /
        fkRectCriticalReducedWeight R q omega := by
  unfold fkRectAllOrientedLoopTilt
  rw [sum_fkRectOrientedLoopWeight_eq_turningProduct]


theorem fkRectAllOrientedLoopTilt_eq_turningProduct_div_loopDefect
    (R : FKRectTorus) {q : Real} (hq : 0 < q) (lam : Real)
    (omega : R.Configuration) :
    fkRectAllOrientedLoopTilt R q lam omega =
      (∏ C : FKMedialLoop R.medialTorus
          (fkRectConfigurationToMedialPairing R omega),
        (Real.exp ((lam / 4) *
            FKMedialTurningFiber.canonicalComponentTurn
              (fkRectConfigurationToMedialPairing R omega) C) +
          Real.exp (-(lam / 4) *
            FKMedialTurningFiber.canonicalComponentTurn
              (fkRectConfigurationToMedialPairing R omega) C))) /
        (Real.sqrt q ^ (R.width * R.height : Nat) *
          Real.sqrt q ^ fkRectMedialLoopCount R omega *
            Real.sqrt q ^ fkRectEulerHomologyDefect R omega) := by
  rw [fkRectAllOrientedLoopTilt_eq_turningProduct]
  rw [fkRectCriticalReducedWeight_eq_loop_defect R hq]

theorem sum_fkRectOrientedLoopWeight_eq_zero_nonzeroTurnPowers_fkQgt4
    (R : FKRectTorus) {q : Real} (hq : 4 < q)
    (omega : R.Configuration) :
    let lam := sixVertexAntiferroelectricLambda (fkQgt4SixVertexWeight q)
    (∑ arrows : SixVertexArrows R.medialTorus,
        fkRectOrientedLoopWeight R lam omega arrows) =
      2 ^ fkRectZeroTurnLoopCount R omega *
        Real.sqrt q ^ fkRectNonzeroTurnLoopCount R omega := by
  dsimp only
  rw [sum_fkRectOrientedLoopWeight_eq_zero_nonzeroTurnPowers,
    exp_add_exp_neg_sixVertexLambda_fkQgt4 hq]


theorem fkRectAllOrientedLoopTilt_eq_zeroTurnLoopCount_fkQgt4
    (R : FKRectTorus) {q : Real} (hq : 4 < q)
    (omega : R.Configuration) :
    let lam := sixVertexAntiferroelectricLambda (fkQgt4SixVertexWeight q)
    fkRectAllOrientedLoopTilt R q lam omega =
      (2 / Real.sqrt q) ^ fkRectZeroTurnLoopCount R omega /
        (Real.sqrt q ^ (R.width * R.height : Nat) *
          Real.sqrt q ^ fkRectEulerHomologyDefect R omega) := by
  dsimp only
  rw [fkRectAllOrientedLoopTilt_eq_turningProduct_div_loopDefect
    R (by linarith)]
  rw [fkRectTurningProduct_eq_zero_nonzeroTurnPowers,
    exp_add_exp_neg_sixVertexLambda_fkQgt4 hq]
  rw [← fkRectZeroTurnLoopCount_add_nonzeroTurnLoopCount R omega,
    pow_add, div_pow]
  have hs : Real.sqrt q ≠ 0 := (Real.sqrt_pos.2 (by linarith)).ne'
  field_simp [hs]


end
end StatMech.FrontierD
