/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSelectedPerron.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFiniteRoots.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBethePhysicalExpansion.Part15
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheSelectedPerron.Part2
open Finset Matrix


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexHasSymmetricBetheIdentification_of_selectedWavePositive
    {c : Real} (hc : 2 < c)
    (hpos : SixVertexSelectedHalfFilledWavePositive c) :
    SixVertexHasSymmetricBetheIdentification c
      (sixVertexPositiveHalfBetheRootFamily hc) := by
  intro k
  have hn : (k + 1) + (k + 1) ≤ sixVertexFourWidth 0 k := by
    unfold sixVertexFourWidth
    omega
  have heq := sixVertexSector_eigenvalue_eq_top_of_positive_eigenvector
    hn (show 0 < c by linarith)
    (sixVertexHalfFilledBetheRealWave hc k) (hpos hc k)
    (sixVertexHalfFilledBetheRealWave_eigenrelation hc k)
  have hhalf : sixVertexFourWidth 0 k / 2 = (k + 1) + (k + 1) := by
    unfold sixVertexFourWidth
    omega
  have heq' : sixVertexSymmetricBetheEigenvalueValue c
        (sixVertexPositiveHalfBetheRoots hc k) =
      sixVertexSectorTopEigenvalue (sixVertexFourWidth 0 k)
        (sixVertexFourWidth 0 k / 2) (Nat.div_le_self _ _) c := by
    simpa only [hhalf] using heq
  unfold sixVertexLambdaAlongFour sixVertexLambda
  simpa only [Nat.sub_zero] using heq'.symm

end
end StatMech.FrontierD
