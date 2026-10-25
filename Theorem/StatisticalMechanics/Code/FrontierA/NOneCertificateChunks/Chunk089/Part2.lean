/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk089.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk089.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts179_checked :
    rawMomentVCounts 179 = generatedVCounts179 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts179_checked :
    rawMomentQCounts 179 = generatedQCounts179 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients179_checked :
    rawMomentStateCoefficientList 179 = generatedStateCoefficients179 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts179_checked, qCounts179_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
