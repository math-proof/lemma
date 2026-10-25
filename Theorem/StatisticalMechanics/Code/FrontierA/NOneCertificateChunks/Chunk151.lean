/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk151.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk151


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts302_checked :
    rawMomentVCounts 302 = generatedVCounts302 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts302_checked :
    rawMomentQCounts 302 = generatedQCounts302 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients302_checked :
    rawMomentStateCoefficientList 302 = generatedStateCoefficients302 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts302_checked, qCounts302_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
