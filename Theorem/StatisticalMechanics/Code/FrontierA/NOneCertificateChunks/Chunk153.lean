/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk153.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk153


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts306_checked :
    rawMomentVCounts 306 = generatedVCounts306 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts306_checked :
    rawMomentQCounts 306 = generatedQCounts306 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients306_checked :
    rawMomentStateCoefficientList 306 = generatedStateCoefficients306 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts306_checked, qCounts306_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
