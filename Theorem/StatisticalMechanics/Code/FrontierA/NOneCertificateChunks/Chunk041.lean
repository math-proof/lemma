/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk041.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk041


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts82_checked :
    rawMomentVCounts 82 = generatedVCounts82 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts82_checked :
    rawMomentQCounts 82 = generatedQCounts82 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients82_checked :
    rawMomentStateCoefficientList 82 = generatedStateCoefficients82 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts82_checked, qCounts82_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
