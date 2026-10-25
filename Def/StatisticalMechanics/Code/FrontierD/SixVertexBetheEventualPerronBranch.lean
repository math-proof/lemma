/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheEventualPerronBranch.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheInfiniteAnisotropyGauge
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheAnalyticCandidateSheet.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheEventualPerronBranch
open Filter Topology


namespace StatMech.FrontierD

noncomputable section

def SixVertexHalfFilledPerronBranchWitness
    (c : Real) (k : Nat) (p : Fin ((k + 1) + (k + 1)) → Real) : Prop :=
  SixVertexOpenRootSimplex p ∧
    SixVertexSatisfiesBetheEquations c (sixVertexFourWidth 0 k)
      ((k + 1) + (k + 1)) p ∧
    sixVertexSymmetricBetheEigenvalueKernel c
        (sixVertexEvenPositiveHalfProjection (k + 1) p) =
      sixVertexSectorTopEigenvalue (sixVertexFourWidth 0 k)
        ((k + 1) + (k + 1)) (by
          unfold sixVertexFourWidth
          omega) c


def SixVertexHalfFilledPerronGaugeWitness
    {c : Real} (hc : 2 < c) (k : Nat) (epsilon : Real)
    (p : Fin ((k + 1) + (k + 1)) → Real) : Prop :=
  SixVertexHalfFilledPerronBranchWitness c k p ∧
    sixVertexWeightedFiniteDensityGauge hc
      (sixVertexFourWidth 0 k) ((k + 1) + (k + 1)) p
      (sixVertexFourierPhysicalDensityMap hc) < epsilon


end
end StatMech.FrontierD
