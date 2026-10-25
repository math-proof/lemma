/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheRegularizedLogBulk.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheRegularizedLogTaylor.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalOffsetConvergence
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalCandidateDecomposition
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheRegularizedLogBulk.Part2


namespace StatMech.FrontierD

open Finset Filter Topology

noncomputable section

def sixVertexCanonicalEvenRegularizedFullLogDisplacement
    {c : Real} (hc : 2 < c) (epsilon : Real) (s k : Nat) : Real :=
  ∑ i, (sixVertexRegularizedBetheLogKernel c epsilon
      (sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k i) -
    sixVertexRegularizedBetheLogKernel c epsilon
      (sixVertexCanonicalEvenAlignedHalfRoots hc s k i))

end
end StatMech.FrontierD
