/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk159.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk159


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts318_checked :
    rawMomentVCounts 318 = generatedVCounts318 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts318_checked :
    rawMomentQCounts 318 = generatedQCounts318 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients318_checked :
    rawMomentStateCoefficientList 318 = generatedStateCoefficients318 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts318_checked, qCounts318_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
