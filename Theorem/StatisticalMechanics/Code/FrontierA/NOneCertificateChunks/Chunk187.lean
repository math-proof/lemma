/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk187.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk187


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts374_checked :
    rawMomentVCounts 374 = generatedVCounts374 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts374_checked :
    rawMomentQCounts 374 = generatedQCounts374 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients374_checked :
    rawMomentStateCoefficientList 374 = generatedStateCoefficients374 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts374_checked, qCounts374_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
