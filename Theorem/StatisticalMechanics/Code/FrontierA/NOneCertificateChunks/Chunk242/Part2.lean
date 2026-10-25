/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk242.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk242.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts485_checked :
    rawMomentVCounts 485 = generatedVCounts485 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts485_checked :
    rawMomentQCounts 485 = generatedQCounts485 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients485_checked :
    rawMomentStateCoefficientList 485 = generatedStateCoefficients485 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts485_checked, qCounts485_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
