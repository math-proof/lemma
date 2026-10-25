/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk105.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk105


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts210_checked :
    rawMomentVCounts 210 = generatedVCounts210 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts210_checked :
    rawMomentQCounts 210 = generatedQCounts210 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients210_checked :
    rawMomentStateCoefficientList 210 = generatedStateCoefficients210 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts210_checked, qCounts210_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
