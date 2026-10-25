/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRightStripConnection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectInducedConditionalLower.Part3
import Theorem.StatisticalMechanics.Code.FK.FKG
import Theorem.StatisticalMechanics.Code.FK.TwoPoint.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRightStripConnection.Part2


namespace StatMech.FrontierD

noncomputable section

def fkRectInducedConnectionChainEvent (R : FKRectTorus)
    (S : Set R.Vertex)
    (t : Finset (FKRectInducedVertex R S × FKRectInducedVertex R S)) :
    Set (ConfigSpace (Sym2 (FKRectInducedVertex R S))) :=
  {omega | ∀ p ∈ t,
    omega ∈ FK.connEvent (fkRectInducedGraph R S) p.1 p.2}

end
end StatMech.FrontierD
