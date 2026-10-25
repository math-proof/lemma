/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk230.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk230


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts460_checked :
    rawMomentVCounts 460 = generatedVCounts460 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts460_checked :
    rawMomentQCounts 460 = generatedQCounts460 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients460_checked :
    rawMomentStateCoefficientList 460 = generatedStateCoefficients460 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts460_checked, qCounts460_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
