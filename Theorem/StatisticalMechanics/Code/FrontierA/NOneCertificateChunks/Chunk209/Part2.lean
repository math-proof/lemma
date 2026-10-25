/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk209.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk209.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts419_checked :
    rawMomentVCounts 419 = generatedVCounts419 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts419_checked :
    rawMomentQCounts 419 = generatedQCounts419 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients419_checked :
    rawMomentStateCoefficientList 419 = generatedStateCoefficients419 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts419_checked, qCounts419_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
