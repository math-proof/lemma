/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk123.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk123.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts247_checked :
    rawMomentVCounts 247 = generatedVCounts247 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts247_checked :
    rawMomentQCounts 247 = generatedQCounts247 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients247_checked :
    rawMomentStateCoefficientList 247 = generatedStateCoefficients247 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts247_checked, qCounts247_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
