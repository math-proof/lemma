/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveEvenPhysicalPairedBranch.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPhysicalPairedBranch.Part2
import Def.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPhysicalCommonFactor.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPhysicalRowCycle.Part11
import Def.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPhysicalParticleHole.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBalancedShareSpectralGapLogConcavity.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByTwoTwoCycleHall.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByTwoCentralPhysicalBranch.Part9
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPositiveEvenPhysicalPairedBranch.Part4
open Filter Matrix Topology


namespace StatMech.FrontierD

noncomputable section

def SixVertexPositiveEvenTracePhysicalPairedBranches
    (N : Nat) (hNpos : 0 < N) (hNeven : Even N) : Prop :=
  forall M n : Nat, (hn0 : 0 < n) -> (hnN : n < N) ->
    Nonempty
      (SixVertexConfigurationPhysicalPairedBranchEmbeddings
        (sixVertexPositiveEvenTorus N M hNpos hNeven)
        ⟨n, by simp [sixVertexPositiveEvenTorus]; omega⟩ hn0 hnN)


def SixVertexPositiveEvenPhysicalPairedBranchHeightStepFactorizations
    (N : Nat) (hNpos : 0 < N) (hNeven : Even N) : Prop :=
  forall M n : Nat, (hn0 : 0 < n) -> (hnN : n < N) ->
    Nonempty
      (SixVertexConfigurationPhysicalCommonFactor
        (sixVertexPositiveEvenTorus N M hNpos hNeven)
        (sixVertexPositiveEvenTorus N (M + 1) hNpos hNeven)
        ⟨n, by simp [sixVertexPositiveEvenTorus]; omega⟩
        ⟨n, by simp [sixVertexPositiveEvenTorus]; omega⟩
        hn0 hnN hn0 hnN)


end
end StatMech.FrontierD
