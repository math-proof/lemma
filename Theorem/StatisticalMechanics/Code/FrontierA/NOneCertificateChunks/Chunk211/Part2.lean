/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk211.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk211.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts423_checked :
    rawMomentVCounts 423 = generatedVCounts423 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts423_checked :
    rawMomentQCounts 423 = generatedQCounts423 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients423_checked :
    rawMomentStateCoefficientList 423 = generatedStateCoefficients423 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts423_checked, qCounts423_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
