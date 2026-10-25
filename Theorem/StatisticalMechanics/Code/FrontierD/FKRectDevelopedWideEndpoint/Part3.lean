/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedWideEndpoint.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDevelopedSquareReflection.Part6
import Def.StatisticalMechanics.Code.FrontierD.FKRectDevelopedWideEndpoint.Part3
open Set


namespace StatMech.FrontierD

open StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem fkRectDevelopedThreeByOneEndpointConnection_imp_torusReachable
    (R : FKRectTorus) (n : Nat)
    (hwidth : 4 * n < R.width) (hheight : 4 * n < R.height)
    (omega : R.Configuration)
    (p : (fkRectDevelopedThreeByOneRect n) ×
      (fkRectDevelopedThreeByOneRect n))
    (hconn : omega ∈
      fkRectDevelopedThreeByOneEndpointConnectionEvent R n p) :
    (fkRectOpenGraph R omega).Reachable
      (fkRectDevelopedSquareVertex R n p.1)
      (fkRectDevelopedSquareVertex R n p.2) := by
  exact hconn.map
    (fkRectDevelopedThreeByOneOpenHom R n hwidth hheight omega)

end
end StatMech.FrontierD
