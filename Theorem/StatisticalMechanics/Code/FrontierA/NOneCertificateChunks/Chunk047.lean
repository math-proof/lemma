/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk047.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk047


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts94_checked :
    rawMomentVCounts 94 = generatedVCounts94 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts94_checked :
    rawMomentQCounts 94 = generatedQCounts94 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients94_checked :
    rawMomentStateCoefficientList 94 = generatedStateCoefficients94 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts94_checked, qCounts94_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
