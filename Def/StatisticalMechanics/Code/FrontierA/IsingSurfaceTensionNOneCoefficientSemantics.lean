/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOneCoefficientSemantics.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOnePolynomialSemantics.Part5


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

noncomputable def weightedListEval (weight : Nat -> Real) : List Int -> Real
  | [] => 0
  | coefficient :: coefficients =>
      (coefficient : Real) * weight 0 +
        weightedListEval (fun i => weight (i + 1)) coefficients

end StatMech.FrontierA.NOneSymmetricMeanCertificate
