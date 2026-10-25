/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheWaveNormalization.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheSelectedPerron.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheWaveNormalization
open Finset Matrix


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexHalfFilledBetheRotatedRealWave_eigenrelation
    {c : Real} (hc : 2 < c) (k : Nat) (a : Complex) :
    sixVertexSectorTransfer (sixVertexFourWidth 0 k)
        ((k + 1) + (k + 1)) c *ᵥ
      sixVertexHalfFilledBetheRotatedRealWave hc k a =
        sixVertexSymmetricBetheEigenvalueValue c
          (sixVertexPositiveHalfBetheRoots hc k) •
            sixVertexHalfFilledBetheRotatedRealWave hc k a := by
  funext x
  have hx := congrFun
    (sixVertexHalfFilledBetheRoots_physicalEigenrelation hc k) x
  change (∑ y, ((sixVertexSectorTransfer (sixVertexFourWidth 0 k)
        ((k + 1) + (k + 1)) c x y : Real) : Complex) *
        sixVertexCoordinateBetheWave c
          (sixVertexHalfFilledBetheRoots hc k) y) =
      sixVertexBetheEigenvalueCandidate c
          (sixVertexHalfFilledBetheRoots hc k) *
        sixVertexCoordinateBetheWave c
          (sixVertexHalfFilledBetheRoots hc k) x at hx
  have hcplx :
      (∑ y, ((sixVertexSectorTransfer (sixVertexFourWidth 0 k)
          ((k + 1) + (k + 1)) c x y : Real) : Complex) *
          (a * sixVertexCoordinateBetheWave c
            (sixVertexHalfFilledBetheRoots hc k) y)) =
        (sixVertexSymmetricBetheEigenvalueValue c
            (sixVertexPositiveHalfBetheRoots hc k) : Complex) *
          (a * sixVertexCoordinateBetheWave c
            (sixVertexHalfFilledBetheRoots hc k) x) := by
    calc
      _ = a * (∑ y,
          ((sixVertexSectorTransfer (sixVertexFourWidth 0 k)
            ((k + 1) + (k + 1)) c x y : Real) : Complex) *
            sixVertexCoordinateBetheWave c
              (sixVertexHalfFilledBetheRoots hc k) y) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro y hy
          ring
      _ = a * (sixVertexBetheEigenvalueCandidate c
            (sixVertexHalfFilledBetheRoots hc k) *
          sixVertexCoordinateBetheWave c
            (sixVertexHalfFilledBetheRoots hc k) x) := by rw [hx]
      _ = _ := by
        rw [sixVertexHalfFilledBetheEigenvalueCandidate_eq_value hc k]
        ring
  have hre := congrArg Complex.re hcplx
  have hsumre :
      ((∑ y, ((sixVertexSectorTransfer (sixVertexFourWidth 0 k)
          ((k + 1) + (k + 1)) c x y : Real) : Complex) *
          (a * sixVertexCoordinateBetheWave c
            (sixVertexHalfFilledBetheRoots hc k) y))).re =
        ∑ y, (((sixVertexSectorTransfer (sixVertexFourWidth 0 k)
          ((k + 1) + (k + 1)) c x y : Real) : Complex) *
          (a * sixVertexCoordinateBetheWave c
            (sixVertexHalfFilledBetheRoots hc k) y)).re := by
    exact map_sum Complex.reCLM _ _
  rw [hsumre] at hre
  simpa only [sixVertexHalfFilledBetheRotatedRealWave, Matrix.mulVec,
    dotProduct, Pi.smul_apply, smul_eq_mul, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] using hre


end
end StatMech.FrontierD
