/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRandomClusterGraphBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectConnectedInsertionCharge.Part2
import Theorem.StatisticalMechanics.Code.FK.RandomCluster.Part6
import Abbrev.StatisticalMechanics.Code.FrontierD.FKRectRandomClusterGraphBridge
open Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

noncomputable def fkRectFullGraphConfiguration
    (R : FKRectTorus) (omega : R.Configuration) :
    ConfigSpace (Sym2 R.Vertex) := by
  classical
  intro e
  exact if he : e ∈ (fkRectTorusGraph R).edgeSet then
    omega ((fkRectEdgeGraphEquiv R).symm ⟨e, he⟩)
  else false

end
end StatMech.FrontierD
