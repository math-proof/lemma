/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk121.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk121


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts242_checked :
    rawMomentVCounts 242 = generatedVCounts242 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts242_checked :
    rawMomentQCounts 242 = generatedQCounts242 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients242_checked :
    rawMomentStateCoefficientList 242 = generatedStateCoefficients242 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts242_checked, qCounts242_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
