/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk047.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk047.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts95_checked :
    rawMomentVCounts 95 = generatedVCounts95 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts95_checked :
    rawMomentQCounts 95 = generatedQCounts95 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients95_checked :
    rawMomentStateCoefficientList 95 = generatedStateCoefficients95 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts95_checked, qCounts95_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
