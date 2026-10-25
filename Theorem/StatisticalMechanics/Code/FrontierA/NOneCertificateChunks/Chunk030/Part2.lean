/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk030.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk030.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts61_checked :
    rawMomentVCounts 61 = generatedVCounts61 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts61_checked :
    rawMomentQCounts 61 = generatedQCounts61 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients61_checked :
    rawMomentStateCoefficientList 61 = generatedStateCoefficients61 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts61_checked, qCounts61_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
