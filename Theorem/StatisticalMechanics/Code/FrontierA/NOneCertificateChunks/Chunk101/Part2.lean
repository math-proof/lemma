/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk101.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk101.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts203_checked :
    rawMomentVCounts 203 = generatedVCounts203 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts203_checked :
    rawMomentQCounts 203 = generatedQCounts203 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients203_checked :
    rawMomentStateCoefficientList 203 = generatedStateCoefficients203 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts203_checked, qCounts203_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
