/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk254.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk254.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts509_checked :
    rawMomentVCounts 509 = generatedVCounts509 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts509_checked :
    rawMomentQCounts 509 = generatedQCounts509 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients509_checked :
    rawMomentStateCoefficientList 509 = generatedStateCoefficients509 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts509_checked, qCounts509_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
