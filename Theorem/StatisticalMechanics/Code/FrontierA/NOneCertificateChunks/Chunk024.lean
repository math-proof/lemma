/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk024.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk024


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts48_checked :
    rawMomentVCounts 48 = generatedVCounts48 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts48_checked :
    rawMomentQCounts 48 = generatedQCounts48 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients48_checked :
    rawMomentStateCoefficientList 48 = generatedStateCoefficients48 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts48_checked, qCounts48_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
