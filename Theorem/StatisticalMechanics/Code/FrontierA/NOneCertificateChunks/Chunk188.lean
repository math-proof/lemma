/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk188.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk188


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts376_checked :
    rawMomentVCounts 376 = generatedVCounts376 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts376_checked :
    rawMomentQCounts 376 = generatedQCounts376 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients376_checked :
    rawMomentStateCoefficientList 376 = generatedStateCoefficients376 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts376_checked, qCounts376_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
