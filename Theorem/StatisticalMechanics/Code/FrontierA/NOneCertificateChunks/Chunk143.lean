/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk143.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk143


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts286_checked :
    rawMomentVCounts 286 = generatedVCounts286 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts286_checked :
    rawMomentQCounts 286 = generatedQCounts286 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients286_checked :
    rawMomentStateCoefficientList 286 = generatedStateCoefficients286 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts286_checked, qCounts286_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
