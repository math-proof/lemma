/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFiniteRoots.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheVariational.Part12
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheScattering.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexCoordinateBethe.Part6
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheThermodynamicReduction.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFiniteRoots


namespace StatMech.FrontierD

noncomputable section

noncomputable def sixVertexHalfFilledBetheCandidateRate
    {c : ℝ} (hc : 2 < c) (k : ℕ) : ℝ :=
  Real.log (sixVertexSymmetricBetheEigenvalueValue c
      (sixVertexPositiveHalfBetheRoots hc k)) /
    (sixVertexFourWidth 0 k : ℝ)

end
end StatMech.FrontierD
