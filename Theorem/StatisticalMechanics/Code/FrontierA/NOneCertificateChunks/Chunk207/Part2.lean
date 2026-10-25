/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk207.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk207.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts415_checked :
    rawMomentVCounts 415 = generatedVCounts415 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts415_checked :
    rawMomentQCounts 415 = generatedQCounts415 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients415_checked :
    rawMomentStateCoefficientList 415 = generatedStateCoefficients415 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts415_checked, qCounts415_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
