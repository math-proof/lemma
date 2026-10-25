/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk230.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk230.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts461_checked :
    rawMomentVCounts 461 = generatedVCounts461 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts461_checked :
    rawMomentQCounts 461 = generatedQCounts461 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients461_checked :
    rawMomentStateCoefficientList 461 = generatedStateCoefficients461 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts461_checked, qCounts461_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
