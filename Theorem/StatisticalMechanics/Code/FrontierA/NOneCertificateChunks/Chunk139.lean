/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk139.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk139


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts278_checked :
    rawMomentVCounts 278 = generatedVCounts278 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts278_checked :
    rawMomentQCounts 278 = generatedQCounts278 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients278_checked :
    rawMomentStateCoefficientList 278 = generatedStateCoefficients278 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts278_checked, qCounts278_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
