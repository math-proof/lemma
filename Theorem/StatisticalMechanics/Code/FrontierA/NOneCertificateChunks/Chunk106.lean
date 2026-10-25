/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk106.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk106


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts212_checked :
    rawMomentVCounts 212 = generatedVCounts212 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts212_checked :
    rawMomentQCounts 212 = generatedQCounts212 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients212_checked :
    rawMomentStateCoefficientList 212 = generatedStateCoefficients212 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts212_checked, qCounts212_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
