/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk181.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk181.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts363_checked :
    rawMomentVCounts 363 = generatedVCounts363 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts363_checked :
    rawMomentQCounts 363 = generatedQCounts363 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients363_checked :
    rawMomentStateCoefficientList 363 = generatedStateCoefficients363 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts363_checked, qCounts363_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
