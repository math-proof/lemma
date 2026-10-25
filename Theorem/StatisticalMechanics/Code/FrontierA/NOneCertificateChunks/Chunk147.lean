/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk147.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk147


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts294_checked :
    rawMomentVCounts 294 = generatedVCounts294 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts294_checked :
    rawMomentQCounts 294 = generatedQCounts294 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients294_checked :
    rawMomentStateCoefficientList 294 = generatedStateCoefficients294 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts294_checked, qCounts294_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
