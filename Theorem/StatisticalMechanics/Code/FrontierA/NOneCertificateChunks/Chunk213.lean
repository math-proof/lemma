/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk213.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk213


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts426_checked :
    rawMomentVCounts 426 = generatedVCounts426 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts426_checked :
    rawMomentQCounts 426 = generatedQCounts426 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients426_checked :
    rawMomentStateCoefficientList 426 = generatedStateCoefficients426 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts426_checked, qCounts426_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
