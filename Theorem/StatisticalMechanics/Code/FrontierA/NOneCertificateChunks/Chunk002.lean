/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk002.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk002


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts4_checked :
    rawMomentVCounts 4 = generatedVCounts4 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts4_checked :
    rawMomentQCounts 4 = generatedQCounts4 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients4_checked :
    rawMomentStateCoefficientList 4 = generatedStateCoefficients4 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts4_checked, qCounts4_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
