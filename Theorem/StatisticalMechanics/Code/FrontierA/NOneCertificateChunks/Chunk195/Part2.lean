/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk195.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk195.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts391_checked :
    rawMomentVCounts 391 = generatedVCounts391 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts391_checked :
    rawMomentQCounts 391 = generatedQCounts391 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients391_checked :
    rawMomentStateCoefficientList 391 = generatedStateCoefficients391 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts391_checked, qCounts391_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
