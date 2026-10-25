/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk136.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk136.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts273_checked :
    rawMomentVCounts 273 = generatedVCounts273 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts273_checked :
    rawMomentQCounts 273 = generatedQCounts273 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients273_checked :
    rawMomentStateCoefficientList 273 = generatedStateCoefficients273 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts273_checked, qCounts273_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
