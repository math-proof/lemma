/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk126.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk126


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts252_checked :
    rawMomentVCounts 252 = generatedVCounts252 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts252_checked :
    rawMomentQCounts 252 = generatedQCounts252 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients252_checked :
    rawMomentStateCoefficientList 252 = generatedStateCoefficients252 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts252_checked, qCounts252_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
