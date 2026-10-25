/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk244.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk244


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts488_checked :
    rawMomentVCounts 488 = generatedVCounts488 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts488_checked :
    rawMomentQCounts 488 = generatedQCounts488 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients488_checked :
    rawMomentStateCoefficientList 488 = generatedStateCoefficients488 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts488_checked, qCounts488_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
