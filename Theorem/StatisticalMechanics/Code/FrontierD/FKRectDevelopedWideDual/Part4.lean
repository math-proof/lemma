/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedWideDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDevelopedWideEndpoint.Part4
import Def.StatisticalMechanics.Code.FrontierD.FKRectDevelopedWideDual.Part4
open Set


namespace StatMech.FrontierD

open StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem fkRectDevelopedThreeByOne_faceDual_connectedWithin_imp_dual
    (R : FKRectTorus) (n : Nat) (hn : 1 ≤ n)
    (hwidth : 4 * n < R.width) (hheight : 4 * n < R.height)
    (omega : R.Configuration)
    {x y : fkRectDevelopedThreeByOneRect n}
    (hxy : ConnectedWithin 2
      (StatMech.Universality.fci_faceDualConfig
        (fkRectDevelopedSquarePullback R n omega))
      (fkRectDevelopedThreeByOneRect n) x y) :
    ConnectedWithin 2
      (fkRectDevelopedSquarePullback R n
        (fkRectDualConfigurationEquiv R omega))
      (fkRectDevelopedThreeByOneRect n) x y := by
  exact hxy.map
    (fkRectDevelopedThreeByOneFaceDualToDualPullbackHom
      R n hn hwidth hheight omega)


end
end StatMech.FrontierD
