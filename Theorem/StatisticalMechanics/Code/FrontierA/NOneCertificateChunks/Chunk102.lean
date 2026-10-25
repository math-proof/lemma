/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk102.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk102


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts204_checked :
    rawMomentVCounts 204 = generatedVCounts204 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts204_checked :
    rawMomentQCounts 204 = generatedQCounts204 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients204_checked :
    rawMomentStateCoefficientList 204 = generatedStateCoefficients204 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts204_checked, qCounts204_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
