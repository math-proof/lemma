/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk027.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk027


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts54_checked :
    rawMomentVCounts 54 = generatedVCounts54 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts54_checked :
    rawMomentQCounts 54 = generatedQCounts54 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients54_checked :
    rawMomentStateCoefficientList 54 = generatedStateCoefficients54 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts54_checked, qCounts54_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
