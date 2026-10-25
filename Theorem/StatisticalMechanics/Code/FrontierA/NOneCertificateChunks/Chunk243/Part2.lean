/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk243.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk243.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts487_checked :
    rawMomentVCounts 487 = generatedVCounts487 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts487_checked :
    rawMomentQCounts 487 = generatedQCounts487 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients487_checked :
    rawMomentStateCoefficientList 487 = generatedStateCoefficients487 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts487_checked, qCounts487_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
