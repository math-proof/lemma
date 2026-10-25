/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalFixedDensityCandidate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalOffsetConvergence
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalFixedChargeReduction.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalFixedDensityCandidate


namespace StatMech.FrontierD

open Filter Topology

noncomputable section

def sixVertexCanonicalFixedEvenDensityCandidateLogRatio
    {c : Real} (hc : 2 < c) (s k : Nat) : Real :=
  Real.log (sixVertexCanonicalFixedEvenDensityBetheEigenvalueValue hc s k) -
    Real.log (sixVertexSymmetricBetheEigenvalueValue c
      (sixVertexCanonicalDensityPerronPositiveHalfRoots hc (2 * s + k)))

def sixVertexCanonicalFixedOddDensityCandidateLogRatio
    {c : Real} (hc : 2 < c) (s k : Nat) : Real :=
  Real.log (sixVertexCanonicalFixedOddDensityBetheEigenvalueValue hc s k) -
    Real.log (sixVertexSymmetricBetheEigenvalueValue c
      (sixVertexCanonicalDensityPerronPositiveHalfRoots hc (2 * s + 1 + k)))

end
end StatMech.FrontierD
