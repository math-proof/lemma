/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk214.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk214.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts429_checked :
    rawMomentVCounts 429 = generatedVCounts429 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts429_checked :
    rawMomentQCounts 429 = generatedQCounts429 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients429_checked :
    rawMomentStateCoefficientList 429 = generatedStateCoefficients429 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts429_checked, qCounts429_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
