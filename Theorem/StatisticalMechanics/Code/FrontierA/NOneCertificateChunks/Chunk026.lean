/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk026.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk026


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts52_checked :
    rawMomentVCounts 52 = generatedVCounts52 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts52_checked :
    rawMomentQCounts 52 = generatedQCounts52 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients52_checked :
    rawMomentStateCoefficientList 52 = generatedStateCoefficients52 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts52_checked, qCounts52_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
