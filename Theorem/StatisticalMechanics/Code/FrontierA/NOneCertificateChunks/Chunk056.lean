/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk056.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk056


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts112_checked :
    rawMomentVCounts 112 = generatedVCounts112 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts112_checked :
    rawMomentQCounts 112 = generatedQCounts112 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients112_checked :
    rawMomentStateCoefficientList 112 = generatedStateCoefficients112 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts112_checked, qCounts112_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
