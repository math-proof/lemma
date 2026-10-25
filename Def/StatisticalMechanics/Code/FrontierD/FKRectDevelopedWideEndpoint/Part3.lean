/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedWideEndpoint.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDevelopedSquareReflection.Part6
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDevelopedWideEndpoint.Part2
open Set


namespace StatMech.FrontierD

open StatMech.Lattice StatMech.RSW.Box

noncomputable section

noncomputable def fkRectDevelopedThreeByOneOpenHom
    (R : FKRectTorus) (n : Nat)
    (hwidth : 4 * n < R.width) (hheight : 4 * n < R.height)
    (omega : R.Configuration) :
    (openSubgraph 2 (fkRectDevelopedSquarePullback R n omega)).induce
        (fkRectDevelopedThreeByOneRect n) →g
      fkRectOpenGraph R omega where
  toFun z := fkRectDevelopedSquareVertex R n z
  map_rel' := by
    intro z w hzw
    change (openSubgraph 2
      (fkRectDevelopedSquarePullback R n omega)).Adj z.1 w.1 at hzw
    rw [openSubgraph_adj] at hzw
    exact (fkRectDevelopedThreeByOnePullback_open_iff
      R n hwidth hheight omega z.2 w.2 hzw.1).mp hzw.2


end
end StatMech.FrontierD
