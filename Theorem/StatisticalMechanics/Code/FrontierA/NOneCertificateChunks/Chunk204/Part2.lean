/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk204.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk204.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts409_checked :
    rawMomentVCounts 409 = generatedVCounts409 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts409_checked :
    rawMomentQCounts 409 = generatedQCounts409 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients409_checked :
    rawMomentStateCoefficientList 409 = generatedStateCoefficients409 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts409_checked, qCounts409_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
