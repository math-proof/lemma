/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexResolvedCrossRoutedKey.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexRoutedUnitFineRelation.Part4
import Instance.StatisticalMechanics.Code.FrontierD.SixVertexResolvedCrossRoutedKey


namespace StatMech.FrontierD

noncomputable section

abbrev FKColoredVertexCrossOccurrence
    {T : EvenTorus} (mask : T.Vertex -> Bool) :=
  {slot : T.Vertex × Bool // mask slot.1 = true}

end
end StatMech.FrontierD
