/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk107.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk107


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts214_checked :
    rawMomentVCounts 214 = generatedVCounts214 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts214_checked :
    rawMomentQCounts 214 = generatedQCounts214 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients214_checked :
    rawMomentStateCoefficientList 214 = generatedStateCoefficients214 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts214_checked, qCounts214_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
