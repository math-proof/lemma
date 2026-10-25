/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk007.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk007.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts15_checked :
    rawMomentVCounts 15 = generatedVCounts15 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts15_checked :
    rawMomentQCounts 15 = generatedQCounts15 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients15_checked :
    rawMomentStateCoefficientList 15 = generatedStateCoefficients15 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts15_checked, qCounts15_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
