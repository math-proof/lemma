/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheWaveNormalization.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheSelectedPerron.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheWaveNormalization.Part2
open Finset Matrix


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexHasSymmetricBetheIdentification_of_selectedWaveHasPositivePhase
    {c : Real} (hc : 2 < c)
    (hpos : SixVertexSelectedHalfFilledWaveHasPositivePhase c) :
    SixVertexHasSymmetricBetheIdentification c
      (sixVertexPositiveHalfBetheRootFamily hc) := by
  intro k
  obtain ⟨a, ha⟩ := hpos hc k
  have hn : (k + 1) + (k + 1) ≤ sixVertexFourWidth 0 k := by
    unfold sixVertexFourWidth
    omega
  have heq := sixVertexSector_eigenvalue_eq_top_of_positive_eigenvector
    hn (show 0 < c by linarith)
    (sixVertexHalfFilledBetheRotatedRealWave hc k a) ha
    (sixVertexHalfFilledBetheRotatedRealWave_eigenrelation hc k a)
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
