/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk186.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk186.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts373_checked :
    rawMomentVCounts 373 = generatedVCounts373 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts373_checked :
    rawMomentQCounts 373 = generatedQCounts373 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients373_checked :
    rawMomentStateCoefficientList 373 = generatedStateCoefficients373 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts373_checked, qCounts373_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
