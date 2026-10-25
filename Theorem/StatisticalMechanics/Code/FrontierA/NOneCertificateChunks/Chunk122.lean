/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk122.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk122


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts244_checked :
    rawMomentVCounts 244 = generatedVCounts244 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts244_checked :
    rawMomentQCounts 244 = generatedQCounts244 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients244_checked :
    rawMomentStateCoefficientList 244 = generatedStateCoefficients244 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts244_checked, qCounts244_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
