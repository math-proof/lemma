/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalFixedEvenPerronBranch.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedChargeContinuationPoint
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalFixedEvenPerronBranch.Part2
open Filter Topology


namespace StatMech.FrontierD

noncomputable section

def SixVertexFixedEvenChargePerronBranchWitness
    (c : Real) (s k : Nat)
    (p : Fin ((s + k + 1) + (s + k + 1)) → Real) : Prop :=
  SixVertexOpenRootSimplex p ∧
    SixVertexSatisfiesBetheEquations c (sixVertexFourWidth (2 * s) k)
      ((s + k + 1) + (s + k + 1)) p ∧
    sixVertexSymmetricBetheEigenvalueKernel c
        (sixVertexEvenPositiveHalfProjection (s + k + 1) p) =
      sixVertexSectorTopEigenvalue (sixVertexFourWidth (2 * s) k)
        ((s + k + 1) + (s + k + 1)) (by
          unfold sixVertexFourWidth
          omega) c


end
end StatMech.FrontierD
