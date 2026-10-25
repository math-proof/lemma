/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk111.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk111.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts223_checked :
    rawMomentVCounts 223 = generatedVCounts223 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts223_checked :
    rawMomentQCounts 223 = generatedQCounts223 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients223_checked :
    rawMomentStateCoefficientList 223 = generatedStateCoefficients223 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts223_checked, qCounts223_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
