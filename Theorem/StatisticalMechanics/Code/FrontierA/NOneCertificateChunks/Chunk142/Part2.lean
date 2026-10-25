/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk142.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk142.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts285_checked :
    rawMomentVCounts 285 = generatedVCounts285 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts285_checked :
    rawMomentQCounts 285 = generatedQCounts285 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients285_checked :
    rawMomentStateCoefficientList 285 = generatedStateCoefficients285 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts285_checked, qCounts285_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
