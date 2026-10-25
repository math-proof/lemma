/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk141.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk141


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts282_checked :
    rawMomentVCounts 282 = generatedVCounts282 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts282_checked :
    rawMomentQCounts 282 = generatedQCounts282 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients282_checked :
    rawMomentStateCoefficientList 282 = generatedStateCoefficients282 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts282_checked, qCounts282_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
