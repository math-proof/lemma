/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk162.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk162


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts324_checked :
    rawMomentVCounts 324 = generatedVCounts324 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts324_checked :
    rawMomentQCounts 324 = generatedQCounts324 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients324_checked :
    rawMomentStateCoefficientList 324 = generatedStateCoefficients324 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts324_checked, qCounts324_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
