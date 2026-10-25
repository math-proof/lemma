/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk069.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk069


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts138_checked :
    rawMomentVCounts 138 = generatedVCounts138 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts138_checked :
    rawMomentQCounts 138 = generatedQCounts138 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients138_checked :
    rawMomentStateCoefficientList 138 = generatedStateCoefficients138 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts138_checked, qCounts138_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
