/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedPairExplicitDecoration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairCTypeHall.Part4
import Abbrev.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairExplicitDecoration.Part4
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem card_sixVertexExplicitMarkedResolution
    {T : EvenTorus} {omega eta : SixVertexArrows T} {k : Nat}
    (decoration : SixVertexExplicitMarkedPairDecoration omega eta k) :
    Fintype.card (SixVertexExplicitMarkedResolution decoration) = 2 ^ k := by
  rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_coe,
    card_sixVertexExplicitUnresolvedSiteFinset]


end
end StatMech.FrontierD
