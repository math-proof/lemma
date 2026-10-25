/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRandomClusterGraphBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectConnectedInsertionCharge.Part2
import Theorem.StatisticalMechanics.Code.FK.RandomCluster.Part6
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRandomClusterGraphBridge.Part5
open Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

def fkRectGraphOpenGraph (R : FKRectTorus)
    (eta : FKRectGraphConfiguration R) : SimpleGraph R.Vertex where
  Adj x y := ∃ e, eta e = true ∧ e.1 = s(x, y)
  symm := by
    constructor
    rintro x y ⟨e, he, hxy⟩
    exact ⟨e, he, by simpa only [Sym2.eq_swap] using hxy⟩
  loopless := ⟨by
    rintro x ⟨e, _, he⟩
    have hedgeset : s(x, x) ∈ (fkRectTorusGraph R).edgeSet := by
      exact he ▸ e.2
    exact (fkRectTorusGraph R).loopless.irrefl x
      ((SimpleGraph.mem_edgeSet (fkRectTorusGraph R)).mp hedgeset)⟩


end
end StatMech.FrontierD
