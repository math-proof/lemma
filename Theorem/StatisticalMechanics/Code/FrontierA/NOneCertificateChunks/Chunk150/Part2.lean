/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk150.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk150.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
theorem vCounts301_checked :
    rawMomentVCounts 301 = generatedVCounts301 := by
  rfl

set_option maxRecDepth 1000000 in
theorem qCounts301_checked :
    rawMomentQCounts 301 = generatedQCounts301 := by
  rfl

set_option maxRecDepth 1000000 in
theorem stateCoefficients301_checked :
    rawMomentStateCoefficientList 301 = generatedStateCoefficients301 := by
  unfold rawMomentStateCoefficientList
  rw [vCounts301_checked, qCounts301_checked]
  rfl


end StatMech.FrontierA.NOneSymmetricMeanCertificate
