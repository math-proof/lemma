/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk250.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk250


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts500_checked :
    rawMomentVCounts 500 = generatedVCounts500 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts500_checked :
    rawMomentQCounts 500 = generatedQCounts500 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients500_checked :
    rawMomentStateCoefficientList 500 = generatedStateCoefficients500 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts500_checked, qCounts500_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
