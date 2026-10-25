/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk092.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk092.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts185_checked :
    rawMomentVCounts 185 = generatedVCounts185 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts185_checked :
    rawMomentQCounts 185 = generatedQCounts185 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients185_checked :
    rawMomentStateCoefficientList 185 = generatedStateCoefficients185 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts185_checked, qCounts185_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
