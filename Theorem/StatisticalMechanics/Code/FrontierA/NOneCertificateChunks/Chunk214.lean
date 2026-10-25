/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk214.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk214


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts428_checked :
    rawMomentVCounts 428 = generatedVCounts428 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts428_checked :
    rawMomentQCounts 428 = generatedQCounts428 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients428_checked :
    rawMomentStateCoefficientList 428 = generatedStateCoefficients428 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts428_checked, qCounts428_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
