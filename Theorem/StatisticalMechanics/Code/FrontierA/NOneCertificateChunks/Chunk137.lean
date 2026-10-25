/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk137.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk137


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts274_checked :
    rawMomentVCounts 274 = generatedVCounts274 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts274_checked :
    rawMomentQCounts 274 = generatedQCounts274 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients274_checked :
    rawMomentStateCoefficientList 274 = generatedStateCoefficients274 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts274_checked, qCounts274_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
