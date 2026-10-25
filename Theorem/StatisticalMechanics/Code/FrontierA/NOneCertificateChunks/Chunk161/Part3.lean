/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/NOneCertificateChunks/Chunk161.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneCertificateCore.Part3
import Def.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk161.Part3


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 100000000 in
theorem coefficientChunk161_checked :
    rawMomentCoefficientSmallList 322 2 = generatedCoefficientChunk161 := by
  unfold rawMomentCoefficientSmallList
  change addCoefficientLists
    (addCoefficientLists (List.replicate 800 0)
      (rawMomentStateCoefficientList 322))
    (rawMomentStateCoefficientList 323) = generatedCoefficientChunk161
  rw [stateCoefficients322_checked, stateCoefficients323_checked]
  rfl

end StatMech.FrontierA.NOneSymmetricMeanCertificate
