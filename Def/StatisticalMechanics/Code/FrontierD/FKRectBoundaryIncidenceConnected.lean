/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryIncidenceConnected.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryCycleDuality.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectPrimalDualClusterLoopCount
import Theorem.StatisticalMechanics.Code.FrontierD.FiniteBipartiteFlowSparse
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryIncidenceConnected
open Equiv Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

noncomputable def fkRectDualBoundarySupportedFiberSum
    (R : FKRectTorus) (omega : R.Configuration)
    (L : (fkRectOpenGraph R
      (fkRectDualConfigurationEquiv R omega)).ConnectedComponent) : Int × Int := by
  classical
  exact ∑ C ∈ ((Finset.univ : Finset
        (FKRectConfigurationBlackBoundaryCycle R omega)).filter fun C ↦
          fkRectBlackBoundaryCycleWinding R omega C ≠ 0).filter
        (fun C ↦ fkRectBlackBoundaryCycleDualComponent R omega C = L),
      fkRectBlackBoundaryCycleWinding R omega C

end
end StatMech.FrontierD
