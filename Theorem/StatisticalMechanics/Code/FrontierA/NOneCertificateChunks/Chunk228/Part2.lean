/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk228.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk228.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts457_checked :
    rawMomentVCounts 457 = generatedVCounts457 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts457_checked :
    rawMomentQCounts 457 = generatedQCounts457 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients457_checked :
    rawMomentStateCoefficientList 457 = generatedStateCoefficients457 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts457_checked, qCounts457_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
