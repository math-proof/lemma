/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk005.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk005


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts10_checked :
    rawMomentVCounts 10 = generatedVCounts10 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts10_checked :
    rawMomentQCounts 10 = generatedQCounts10 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients10_checked :
    rawMomentStateCoefficientList 10 = generatedStateCoefficients10 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts10_checked, qCounts10_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
