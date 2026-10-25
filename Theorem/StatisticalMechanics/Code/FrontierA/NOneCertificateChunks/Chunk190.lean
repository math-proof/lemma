/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk190.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk190


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts380_checked :
    rawMomentVCounts 380 = generatedVCounts380 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts380_checked :
    rawMomentQCounts 380 = generatedQCounts380 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients380_checked :
    rawMomentStateCoefficientList 380 = generatedStateCoefficients380 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts380_checked, qCounts380_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
