/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk215.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk215.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts431_checked :
    rawMomentVCounts 431 = generatedVCounts431 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts431_checked :
    rawMomentQCounts 431 = generatedQCounts431 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients431_checked :
    rawMomentStateCoefficientList 431 = generatedStateCoefficients431 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts431_checked, qCounts431_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
