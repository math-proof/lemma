/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSelectedPerron.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFiniteRoots.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBethePhysicalExpansion.Part15
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheSelectedPerron
open Finset Matrix


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexHalfFilledBetheRealWave_eigenrelation
    {c : Real} (hc : 2 < c) (k : Nat) :
    sixVertexSectorTransfer (sixVertexFourWidth 0 k)
        ((k + 1) + (k + 1)) c *ᵥ
      sixVertexHalfFilledBetheRealWave hc k =
        sixVertexSymmetricBetheEigenvalueValue c
          (sixVertexPositiveHalfBetheRoots hc k) •
            sixVertexHalfFilledBetheRealWave hc k := by
  funext x
  have hx := congrFun
    (sixVertexHalfFilledBetheRoots_physicalEigenrelation hc k) x
  have hre := congrArg Complex.re hx
  simp only [sixVertexSectorTransferComplex_mulVec_apply,
    sixVertexHalfFilledBetheEigenvalueCandidate_eq_value hc k,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero, Pi.smul_apply, smul_eq_mul] at hre
  simpa [sixVertexHalfFilledBetheRealWave, Matrix.mulVec, dotProduct,
    smul_eq_mul] using hre


end
end StatMech.FrontierD
