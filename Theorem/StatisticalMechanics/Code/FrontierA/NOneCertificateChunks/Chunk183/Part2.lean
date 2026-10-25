/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk183.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk183.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts367_checked :
    rawMomentVCounts 367 = generatedVCounts367 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts367_checked :
    rawMomentQCounts 367 = generatedQCounts367 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients367_checked :
    rawMomentStateCoefficientList 367 = generatedStateCoefficients367 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts367_checked, qCounts367_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
