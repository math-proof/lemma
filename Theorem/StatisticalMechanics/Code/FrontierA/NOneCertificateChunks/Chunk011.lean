/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk011.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk011


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts22_checked :
    rawMomentVCounts 22 = generatedVCounts22 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts22_checked :
    rawMomentQCounts 22 = generatedQCounts22 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients22_checked :
    rawMomentStateCoefficientList 22 = generatedStateCoefficients22 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts22_checked, qCounts22_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
