/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk133.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk133.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts267_checked :
    rawMomentVCounts 267 = generatedVCounts267 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts267_checked :
    rawMomentQCounts 267 = generatedQCounts267 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients267_checked :
    rawMomentStateCoefficientList 267 = generatedStateCoefficients267 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts267_checked, qCounts267_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
