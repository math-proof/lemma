/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk032.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk032.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts65_checked :
    rawMomentVCounts 65 = generatedVCounts65 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts65_checked :
    rawMomentQCounts 65 = generatedQCounts65 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients65_checked :
    rawMomentStateCoefficientList 65 = generatedStateCoefficients65 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts65_checked, qCounts65_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
