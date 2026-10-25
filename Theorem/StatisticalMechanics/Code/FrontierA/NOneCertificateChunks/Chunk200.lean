/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk200.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk200


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts400_checked :
    rawMomentVCounts 400 = generatedVCounts400 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts400_checked :
    rawMomentQCounts 400 = generatedQCounts400 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients400_checked :
    rawMomentStateCoefficientList 400 = generatedStateCoefficients400 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts400_checked, qCounts400_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
