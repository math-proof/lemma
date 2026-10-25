/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk160.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk160.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts321_checked :
    rawMomentVCounts 321 = generatedVCounts321 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts321_checked :
    rawMomentQCounts 321 = generatedQCounts321 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients321_checked :
    rawMomentStateCoefficientList 321 = generatedStateCoefficients321 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts321_checked, qCounts321_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
