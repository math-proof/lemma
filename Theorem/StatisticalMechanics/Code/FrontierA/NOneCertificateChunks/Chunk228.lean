/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk228.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk228


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts456_checked :
    rawMomentVCounts 456 = generatedVCounts456 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts456_checked :
    rawMomentQCounts 456 = generatedQCounts456 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients456_checked :
    rawMomentStateCoefficientList 456 = generatedStateCoefficients456 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts456_checked, qCounts456_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
