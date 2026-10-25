/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk059.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk059


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts118_checked :
    rawMomentVCounts 118 = generatedVCounts118 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts118_checked :
    rawMomentQCounts 118 = generatedQCounts118 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients118_checked :
    rawMomentStateCoefficientList 118 = generatedStateCoefficients118 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts118_checked, qCounts118_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
