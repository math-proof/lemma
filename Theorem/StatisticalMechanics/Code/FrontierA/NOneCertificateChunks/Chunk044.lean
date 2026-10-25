/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk044.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk044


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts88_checked :
    rawMomentVCounts 88 = generatedVCounts88 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts88_checked :
    rawMomentQCounts 88 = generatedQCounts88 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients88_checked :
    rawMomentStateCoefficientList 88 = generatedStateCoefficients88 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts88_checked, qCounts88_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
