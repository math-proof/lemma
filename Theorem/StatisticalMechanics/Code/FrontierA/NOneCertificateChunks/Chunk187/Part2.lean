/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk187.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk187.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts375_checked :
    rawMomentVCounts 375 = generatedVCounts375 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts375_checked :
    rawMomentQCounts 375 = generatedQCounts375 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients375_checked :
    rawMomentStateCoefficientList 375 = generatedStateCoefficients375 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts375_checked, qCounts375_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
