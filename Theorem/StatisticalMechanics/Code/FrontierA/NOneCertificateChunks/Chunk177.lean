/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk177.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk177


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts354_checked :
    rawMomentVCounts 354 = generatedVCounts354 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts354_checked :
    rawMomentQCounts 354 = generatedQCounts354 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients354_checked :
    rawMomentStateCoefficientList 354 = generatedStateCoefficients354 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts354_checked, qCounts354_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
