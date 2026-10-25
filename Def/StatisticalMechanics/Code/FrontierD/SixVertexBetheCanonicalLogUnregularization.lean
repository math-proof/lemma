/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalLogUnregularization.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheLogRegularizationCutoff
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalRegularizedQuadrature
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalLogUnregularization


namespace StatMech.FrontierD

open Filter Topology Finset

noncomputable section

def sixVertexCanonicalEvenBulkLogDisplacement
    {c : Real} (hc : 2 < c) (s k : Nat) : Real :=
  ∑ j, (sixVertexBetheLogObservable c
      (sixVertexCanonicalFixedEvenDensityPositiveRoots hc s k j) -
    sixVertexBetheLogObservable c
      (sixVertexCanonicalEvenCommonHalfRoot hc s k j))

end
end StatMech.FrontierD
