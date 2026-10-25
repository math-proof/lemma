/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk015.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk015.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts31_checked :
    rawMomentVCounts 31 = generatedVCounts31 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts31_checked :
    rawMomentQCounts 31 = generatedQCounts31 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients31_checked :
    rawMomentStateCoefficientList 31 = generatedStateCoefficients31 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts31_checked, qCounts31_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
