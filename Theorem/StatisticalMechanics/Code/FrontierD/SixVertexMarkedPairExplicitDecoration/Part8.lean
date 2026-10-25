/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedPairExplicitDecoration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairCTypeHall.Part4
import Def.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairExplicitDecoration.Part6
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexExplicitResolvedPairing_eq_of_partial_eq_some
    {T : EvenTorus} {omega eta : SixVertexArrows T} {k : Nat}
    (decoration : SixVertexExplicitMarkedPairDecoration omega eta k)
    (resolution : SixVertexExplicitMarkedResolution decoration)
    (layer : Bool) (v : T.Vertex) (pairing : Bool)
    (hpairing : sixVertexExplicitMarkedPartialPairing
      decoration layer v = some pairing) :
    sixVertexExplicitResolvedPairing decoration resolution layer v =
      pairing := by
  simp [sixVertexExplicitResolvedPairing, hpairing]

theorem sixVertexExplicitResolvedPairing_eq_resolution
    {T : EvenTorus} {omega eta : SixVertexArrows T} {k : Nat}
    (decoration : SixVertexExplicitMarkedPairDecoration omega eta k)
    (resolution : SixVertexExplicitMarkedResolution decoration)
    (site : {x : Bool × T.Vertex //
      x ∈ sixVertexExplicitUnresolvedSiteFinset decoration}) :
    sixVertexExplicitResolvedPairing decoration resolution
        site.1.1 site.1.2 = resolution site := by
  have hnone : sixVertexExplicitMarkedPartialPairing decoration
      site.1.1 site.1.2 = none := by
    simpa only [sixVertexExplicitUnresolvedSiteFinset,
      Finset.mem_filter, Finset.mem_univ, true_and] using site.2
  simp [sixVertexExplicitResolvedPairing, hnone]

theorem sixVertexExplicitMarkedPartialPairing_compatible
    {T : EvenTorus} {omega eta : SixVertexArrows T} {k : Nat}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (decoration : SixVertexExplicitMarkedPairDecoration omega eta k)
    (layer : Bool) (v : T.Vertex) (pairing : Bool)
    (hpairing : sixVertexExplicitMarkedPartialPairing
      decoration layer v = some pairing) :
    fkLoopPairingCompatible pairing
      (sixVertexArrowPairLayer omega eta layer) v := by
  dsimp only [sixVertexExplicitMarkedPartialPairing] at hpairing
  split at hpairing
  · rename_i hc
    split at hpairing
    · simp at hpairing
    ·
      apply fkLoopPairingCompatible_of_cType
      · cases layer
        · exact homega
        · exact heta
      · exact hc
  · rename_i hc
    have hp : pairing = sixVertexPreferredCompatiblePairing
        (sixVertexArrowPairLayer omega eta layer) v := by
      simpa using hpairing.symm
    subst pairing
    apply sixVertexPreferredCompatiblePairing_compatible
    cases layer
    · exact homega
    · exact heta

theorem sixVertexExplicitResolvedPairing_compatible
    {T : EvenTorus} {omega eta : SixVertexArrows T} {k : Nat}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (decoration : SixVertexExplicitMarkedPairDecoration omega eta k)
    (resolution : SixVertexExplicitMarkedResolution decoration)
    (layer : Bool) (v : T.Vertex) :
    fkLoopPairingCompatible
      (sixVertexExplicitResolvedPairing decoration resolution layer v)
      (sixVertexArrowPairLayer omega eta layer) v := by
  by_cases hnone : sixVertexExplicitMarkedPartialPairing
      decoration layer v = none
  · apply fkLoopPairingCompatible_of_cType
    · cases layer
      · exact homega
      · exact heta
    · obtain ⟨site, hsite, hval⟩ :=
        (sixVertexExplicitMarkedPartialPairing_eq_none_iff
          decoration layer v).mp hnone
      simpa [sixVertexArrowPairLayer, hval] using site.2
  · obtain ⟨pairing, hpairing⟩ :=
      Option.ne_none_iff_exists'.mp hnone
    rw [sixVertexExplicitResolvedPairing_eq_of_partial_eq_some
      decoration resolution layer v pairing hpairing]
    exact sixVertexExplicitMarkedPartialPairing_compatible
      homega heta decoration layer v pairing hpairing

theorem card_sixVertexExplicitMarkedPairDecoration
    {T : EvenTorus} (omega eta : SixVertexArrows T) (k : Nat) :
    Fintype.card (SixVertexExplicitMarkedPairDecoration omega eta k) =
      sixVertexMarkedPairMultiplicityNat omega eta k := by
  rw [card_markedBinaryDecoration, card_sixVertexPairCTypeSite]
  rfl


end
end StatMech.FrontierD
