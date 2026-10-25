/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk242.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk242


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts484_checked :
    rawMomentVCounts 484 = generatedVCounts484 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts484_checked :
    rawMomentQCounts 484 = generatedQCounts484 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients484_checked :
    rawMomentStateCoefficientList 484 = generatedStateCoefficients484 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts484_checked, qCounts484_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
