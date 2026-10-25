/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk227.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk227.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts455_checked :
    rawMomentVCounts 455 = generatedVCounts455 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts455_checked :
    rawMomentQCounts 455 = generatedQCounts455 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients455_checked :
    rawMomentStateCoefficientList 455 = generatedStateCoefficients455 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts455_checked, qCounts455_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
