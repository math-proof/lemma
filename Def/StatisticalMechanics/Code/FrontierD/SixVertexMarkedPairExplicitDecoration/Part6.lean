/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedPairExplicitDecoration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairCTypeHall.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairExplicitDecoration.Part7
open Finset


namespace StatMech.FrontierD

noncomputable section

noncomputable def sixVertexExplicitMarkedResolutionEquivFin
    {T : EvenTorus} {omega eta : SixVertexArrows T} {k : Nat}
    (decoration : SixVertexExplicitMarkedPairDecoration omega eta k) :
    SixVertexExplicitMarkedResolution decoration ≃ Fin (2 ^ k) := by
  apply Fintype.equivOfCardEq
  rw [Fintype.card_fin, card_sixVertexExplicitMarkedResolution]


noncomputable def sixVertexExplicitResolvedPairing
    {T : EvenTorus} {omega eta : SixVertexArrows T} {k : Nat}
    (decoration : SixVertexExplicitMarkedPairDecoration omega eta k)
    (resolution : SixVertexExplicitMarkedResolution decoration)
    (layer : Bool) (v : T.Vertex) : Bool :=
  if hnone : sixVertexExplicitMarkedPartialPairing decoration layer v = none
  then resolution ⟨(layer, v), by
    simp [sixVertexExplicitUnresolvedSiteFinset, hnone]⟩
  else
    (sixVertexExplicitMarkedPartialPairing decoration layer v).get
      (Option.isSome_iff_ne_none.mpr hnone)

end
end StatMech.FrontierD
