/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk197.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk197.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts395_checked :
    rawMomentVCounts 395 = generatedVCounts395 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts395_checked :
    rawMomentQCounts 395 = generatedQCounts395 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients395_checked :
    rawMomentStateCoefficientList 395 = generatedStateCoefficients395 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts395_checked, qCounts395_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
