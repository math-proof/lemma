/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk191.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk191.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts383_checked :
    rawMomentVCounts 383 = generatedVCounts383 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts383_checked :
    rawMomentQCounts 383 = generatedQCounts383 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients383_checked :
    rawMomentStateCoefficientList 383 = generatedStateCoefficients383 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts383_checked, qCounts383_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
