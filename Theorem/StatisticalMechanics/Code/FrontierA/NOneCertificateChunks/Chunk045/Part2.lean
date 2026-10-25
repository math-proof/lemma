/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk045.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk045.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts91_checked :
    rawMomentVCounts 91 = generatedVCounts91 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts91_checked :
    rawMomentQCounts 91 = generatedQCounts91 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients91_checked :
    rawMomentStateCoefficientList 91 = generatedStateCoefficients91 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts91_checked, qCounts91_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
