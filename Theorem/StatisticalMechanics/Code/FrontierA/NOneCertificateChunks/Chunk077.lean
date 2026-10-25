/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk077.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk077


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts154_checked :
    rawMomentVCounts 154 = generatedVCounts154 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts154_checked :
    rawMomentQCounts 154 = generatedQCounts154 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients154_checked :
    rawMomentStateCoefficientList 154 = generatedStateCoefficients154 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts154_checked, qCounts154_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
