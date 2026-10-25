/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk146.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk146.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts293_checked :
    rawMomentVCounts 293 = generatedVCounts293 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts293_checked :
    rawMomentQCounts 293 = generatedQCounts293 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients293_checked :
    rawMomentStateCoefficientList 293 = generatedStateCoefficients293 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts293_checked, qCounts293_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
