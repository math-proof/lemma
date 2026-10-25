/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk096.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk096.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts193_checked :
    rawMomentVCounts 193 = generatedVCounts193 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts193_checked :
    rawMomentQCounts 193 = generatedQCounts193 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients193_checked :
    rawMomentStateCoefficientList 193 = generatedStateCoefficients193 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts193_checked, qCounts193_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
