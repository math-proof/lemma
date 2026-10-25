/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk013.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk013.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts27_checked :
    rawMomentVCounts 27 = generatedVCounts27 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts27_checked :
    rawMomentQCounts 27 = generatedQCounts27 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients27_checked :
    rawMomentStateCoefficientList 27 = generatedStateCoefficients27 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts27_checked, qCounts27_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
