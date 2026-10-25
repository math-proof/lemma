/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk147.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk147.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts295_checked :
    rawMomentVCounts 295 = generatedVCounts295 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts295_checked :
    rawMomentQCounts 295 = generatedQCounts295 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients295_checked :
    rawMomentStateCoefficientList 295 = generatedStateCoefficients295 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts295_checked, qCounts295_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
