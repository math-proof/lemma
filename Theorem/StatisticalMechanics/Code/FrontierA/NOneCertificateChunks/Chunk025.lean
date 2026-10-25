/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk025.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk025


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts50_checked :
    rawMomentVCounts 50 = generatedVCounts50 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts50_checked :
    rawMomentQCounts 50 = generatedQCounts50 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients50_checked :
    rawMomentStateCoefficientList 50 = generatedStateCoefficients50 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts50_checked, qCounts50_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
