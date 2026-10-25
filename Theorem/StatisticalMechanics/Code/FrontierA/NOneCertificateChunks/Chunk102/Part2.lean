/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk102.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk102.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts205_checked :
    rawMomentVCounts 205 = generatedVCounts205 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts205_checked :
    rawMomentQCounts 205 = generatedQCounts205 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients205_checked :
    rawMomentStateCoefficientList 205 = generatedStateCoefficients205 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts205_checked, qCounts205_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
