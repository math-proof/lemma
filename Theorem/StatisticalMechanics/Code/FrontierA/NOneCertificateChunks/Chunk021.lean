/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk021.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk021


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts42_checked :
    rawMomentVCounts 42 = generatedVCounts42 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts42_checked :
    rawMomentQCounts 42 = generatedQCounts42 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients42_checked :
    rawMomentStateCoefficientList 42 = generatedStateCoefficients42 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts42_checked, qCounts42_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
