/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalFixedDensityCandidate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalOffsetConvergence
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalFixedChargeReduction.Part2


namespace StatMech.FrontierD

open Filter Topology

noncomputable section

def sixVertexCanonicalFixedEvenDensityBetheEigenvalueValue
    {c : Real} (hc : 2 < c) (s k : Nat) : Real :=
  sixVertexSymmetricBetheEigenvalueValue c
    (sixVertexEvenPositiveHalfProjection (s + k + 1)
      (sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k))

def sixVertexCanonicalFixedOddDensityBetheEigenvalueValue
    {c : Real} (hc : 2 < c) (s k : Nat) : Real :=
  sixVertexZeroPhaseBetheEigenvalueValue c
    (sixVertexFourWidth (2 * s + 1) k)
    (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k)
    (sixVertexOddCentralIndex (s + k + 1))

def sixVertexCanonicalFixedEvenDensityPositiveRoots
    {c : Real} (hc : 2 < c) (s k : Nat) : Fin (s + k + 1) -> Real :=
  sixVertexEvenPositiveHalfProjection (s + k + 1)
    (sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k)

def sixVertexCanonicalFixedOddDensityPositiveRoots
    {c : Real} (hc : 2 < c) (s k : Nat) : Fin (s + k + 1) -> Real :=
  sixVertexOddPositiveHalfProjection (s + k + 1)
    (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k)

end
end StatMech.FrontierD
