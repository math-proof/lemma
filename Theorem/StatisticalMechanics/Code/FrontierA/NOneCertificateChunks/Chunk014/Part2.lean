/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk014.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk014.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts29_checked :
    rawMomentVCounts 29 = generatedVCounts29 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts29_checked :
    rawMomentQCounts 29 = generatedQCounts29 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients29_checked :
    rawMomentStateCoefficientList 29 = generatedStateCoefficients29 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts29_checked, qCounts29_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
