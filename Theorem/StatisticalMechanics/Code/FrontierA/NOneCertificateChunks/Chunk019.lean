/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk019.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk019


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts38_checked :
    rawMomentVCounts 38 = generatedVCounts38 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts38_checked :
    rawMomentQCounts 38 = generatedQCounts38 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients38_checked :
    rawMomentStateCoefficientList 38 = generatedStateCoefficients38 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts38_checked, qCounts38_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
