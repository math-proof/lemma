/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk235.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk235


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts470_checked :
    rawMomentVCounts 470 = generatedVCounts470 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts470_checked :
    rawMomentQCounts 470 = generatedQCounts470 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients470_checked :
    rawMomentStateCoefficientList 470 = generatedStateCoefficients470 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts470_checked, qCounts470_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
