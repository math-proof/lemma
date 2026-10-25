/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk103.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk103


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts206_checked :
    rawMomentVCounts 206 = generatedVCounts206 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts206_checked :
    rawMomentQCounts 206 = generatedQCounts206 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients206_checked :
    rawMomentStateCoefficientList 206 = generatedStateCoefficients206 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts206_checked, qCounts206_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
