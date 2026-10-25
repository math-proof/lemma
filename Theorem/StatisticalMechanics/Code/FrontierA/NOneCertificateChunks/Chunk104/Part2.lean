/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk104.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk104.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts209_checked :
    rawMomentVCounts 209 = generatedVCounts209 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts209_checked :
    rawMomentQCounts 209 = generatedQCounts209 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients209_checked :
    rawMomentStateCoefficientList 209 = generatedStateCoefficients209 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts209_checked, qCounts209_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
