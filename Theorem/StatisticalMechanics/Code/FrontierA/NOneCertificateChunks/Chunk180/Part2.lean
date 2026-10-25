/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk180.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk180.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts361_checked :
    rawMomentVCounts 361 = generatedVCounts361 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts361_checked :
    rawMomentQCounts 361 = generatedQCounts361 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients361_checked :
    rawMomentStateCoefficientList 361 = generatedStateCoefficients361 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts361_checked, qCounts361_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
