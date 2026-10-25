/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk006.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk006.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts13_checked :
    rawMomentVCounts 13 = generatedVCounts13 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts13_checked :
    rawMomentQCounts 13 = generatedQCounts13 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients13_checked :
    rawMomentStateCoefficientList 13 = generatedStateCoefficients13 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts13_checked, qCounts13_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
