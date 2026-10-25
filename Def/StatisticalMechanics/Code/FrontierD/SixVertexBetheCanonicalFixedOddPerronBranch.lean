/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalFixedOddPerronBranch.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalFixedEvenPerronBranch.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedOddChargeContinuation.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheOddAnalyticCandidateSheet
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalFixedOddPerronBranch
open Filter Topology


namespace StatMech.FrontierD

noncomputable section

def SixVertexFixedOddChargePerronBranchWitness
    (c : Real) (s k : Nat)
    (p : Fin (((s + k + 1) + 1) + (s + k + 1)) → Real) : Prop :=
  SixVertexOpenRootSimplex p ∧
    SixVertexSatisfiesBetheEquations c
      (sixVertexFourWidth (2 * s + 1) k)
      (((s + k + 1) + 1) + (s + k + 1)) p ∧
    sixVertexZeroPhaseBetheEigenvalueValue c
        (sixVertexFourWidth (2 * s + 1) k) p
        (sixVertexOddCentralIndex (s + k + 1)) =
      sixVertexSectorTopEigenvalue (sixVertexFourWidth (2 * s + 1) k)
        (((s + k + 1) + 1) + (s + k + 1)) (by
          unfold sixVertexFourWidth
          omega) c

end
end StatMech.FrontierD
