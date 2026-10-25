/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk222.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk222


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts444_checked :
    rawMomentVCounts 444 = generatedVCounts444 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts444_checked :
    rawMomentQCounts 444 = generatedQCounts444 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients444_checked :
    rawMomentStateCoefficientList 444 = generatedStateCoefficients444 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts444_checked, qCounts444_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
