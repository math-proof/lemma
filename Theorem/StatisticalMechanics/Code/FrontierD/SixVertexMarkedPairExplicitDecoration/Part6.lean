/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedPairExplicitDecoration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairCTypeHall.Part4
import Def.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairExplicitDecoration.Part5
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexExplicitUnresolvedSiteFinset_eq_projection
    {T : EvenTorus} {omega eta : SixVertexArrows T} {k : Nat}
    (decoration : SixVertexExplicitMarkedPairDecoration omega eta k) :
    sixVertexExplicitUnresolvedSiteFinset decoration =
      sixVertexExplicitMarkedSiteProjection decoration := by
  ext x
  rcases x with ⟨layer, v⟩
  simp [sixVertexExplicitUnresolvedSiteFinset,
    mem_sixVertexExplicitMarkedSiteProjection_iff,
    sixVertexExplicitMarkedPartialPairing_eq_none_iff]

theorem card_sixVertexExplicitUnresolvedSiteFinset
    {T : EvenTorus} {omega eta : SixVertexArrows T} {k : Nat}
    (decoration : SixVertexExplicitMarkedPairDecoration omega eta k) :
    (sixVertexExplicitUnresolvedSiteFinset decoration).card = k := by
  rw [sixVertexExplicitUnresolvedSiteFinset_eq_projection]
  simp [sixVertexExplicitMarkedSiteProjection, decoration.1.2]


end
end StatMech.FrontierD
