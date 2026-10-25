/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexResolvedCrossRoutedKey.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexRoutedUnitFineRelation.Part4
import Abbrev.StatisticalMechanics.Code.FrontierD.SixVertexResolvedCrossRoutedKey


namespace StatMech.FrontierD

noncomputable section

noncomputable def fkColoredVertexCrossOccurrenceKey
    {T : EvenTorus} (mask : T.Vertex -> Bool)
    (_layer : Bool)
    (i : Fin (Fintype.card (FKColoredVertexCrossOccurrence mask))) :
    T.Vertex × Bool :=
  ((Fintype.equivFin (FKColoredVertexCrossOccurrence mask)).symm i).1

end
end StatMech.FrontierD
