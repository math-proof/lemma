/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedWideEndpoint.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDevelopedSquareReflection.Part6
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDevelopedWideEndpoint
open Set


namespace StatMech.FrontierD

open StatMech.Lattice StatMech.RSW.Box

noncomputable section

def fkRectDevelopedThreeByOneEndpointConnectionEvent
    (R : FKRectTorus) (n : Nat)
    (p : (fkRectDevelopedThreeByOneRect n) ×
      (fkRectDevelopedThreeByOneRect n)) : Set R.Configuration :=
  {omega | ConnectedWithin 2 (fkRectDevelopedSquarePullback R n omega)
    (fkRectDevelopedThreeByOneRect n) p.1 p.2}


end
end StatMech.FrontierD
