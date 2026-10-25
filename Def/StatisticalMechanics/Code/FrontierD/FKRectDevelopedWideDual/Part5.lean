/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedWideDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDevelopedWideEndpoint.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDevelopedWideDual.Part4
open Set


namespace StatMech.FrontierD

open StatMech.Lattice StatMech.RSW.Box

noncomputable section

def fkRectDevelopedThreeByOneFaceDualHorizontalEvent
    (R : FKRectTorus) (n : Nat) : Set R.Configuration :=
  {omega | HorizontalCrossing
    (StatMech.Universality.fci_faceDualConfig
      (fkRectDevelopedSquarePullback R n omega))
    0 (3 * (n : Int)) 0 n}


end
end StatMech.FrontierD
