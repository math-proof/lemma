/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk149.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk149


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts298_checked :
    rawMomentVCounts 298 = generatedVCounts298 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts298_checked :
    rawMomentQCounts 298 = generatedQCounts298 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients298_checked :
    rawMomentStateCoefficientList 298 = generatedStateCoefficients298 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts298_checked, qCounts298_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
