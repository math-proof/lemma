/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk118.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk118.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts237_checked :
    rawMomentVCounts 237 = generatedVCounts237 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts237_checked :
    rawMomentQCounts 237 = generatedQCounts237 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients237_checked :
    rawMomentStateCoefficientList 237 = generatedStateCoefficients237 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts237_checked, qCounts237_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
