/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOddLogUnregularization.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalLogUnregularization.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalOddOffsetLinear.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalOddLogInterface.Part2


namespace StatMech.FrontierD

open Filter Topology Finset

noncomputable section

def sixVertexCanonicalOddRegularizedBulkLogDisplacement
    {c : Real} (hc : 2 < c) (epsilon : Real) (s k : Nat) : Real :=
  ∑ j, (sixVertexRegularizedBetheLogKernel c epsilon
      (sixVertexCanonicalFixedOddDensityPositiveRoots hc s k j) -
    sixVertexRegularizedBetheLogKernel c epsilon
      (sixVertexCanonicalOddMidpointHalfRoot hc s k j))

def sixVertexCanonicalOddEffectiveOffsetLinearBound
    (c : Real) (hc : 2 < c) (s : Nat) : Real :=
  sixVertexCanonicalOddOffsetLinearBound c hc s +
    sixVertexCanonicalOddOffsetRemainderBound c hc s / Real.pi

end
end StatMech.FrontierD
