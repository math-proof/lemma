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


namespace StatMech.FrontierD

open Finset Filter Topology

noncomputable section

def sixVertexCanonicalEvenRegularizedBulkLogDisplacement
    {c : Real} (hc : 2 < c) (epsilon : Real) (s k : Nat) : Real :=
  ∑ j, (sixVertexRegularizedBetheLogKernel c epsilon
      (sixVertexCanonicalFixedEvenDensityPositiveRoots hc s k j) -
    sixVertexRegularizedBetheLogKernel c epsilon
      (sixVertexCanonicalEvenCommonHalfRoot hc s k j))

end
end StatMech.FrontierD
