import Mathlib
import sympy.Basic
import Def.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairExplicitDecoration.Part8
open Finset StatMech StatMech.FrontierD


/--
[card_complement_subtype](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedPairExplicitDecoration.lean)
-/
@[path]
private lemma card_complement_subtype_eq
  [Fintype Site]
  [DecidableEq Site]
  {marked : Finset Site} :
-- imply
  Fintype.card {site : Site // site ∉ marked} = Fintype.card Site - marked.card := by
-- proof
  apply StatMech.FrontierD.card_complement_subtype marked

/--
[card_marked_finsets](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedPairExplicitDecoration.lean)
-/
@[path]
private lemma card_marked_finsets_eq
  {Site : Type*}
  [Fintype Site]
  [DecidableEq Site]
  {k : Nat} :
-- imply
  Fintype.card {s : Finset Site // s.card = k} = (Fintype.card Site).choose k := by
-- proof
  apply StatMech.FrontierD.card_marked_finsets Site k

/--
[card_markedBinaryDecoration](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedPairExplicitDecoration.lean)
-/
@[path]
private lemma card_markedBinaryDecoration_eq
  {Site : Type*}
  [Fintype Site]
  [DecidableEq Site]
  {k : Nat} :
-- imply
  Fintype.card (MarkedBinaryDecoration Site k) = 2 ^ (Fintype.card Site - k) * (Fintype.card Site).choose k := by
-- proof
  apply StatMech.FrontierD.card_markedBinaryDecoration Site k

/--
[card_cTypeSite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedPairExplicitDecoration.lean)
-/
@[path]
private lemma card_cTypeSite_eq
  {T : EvenTorus}
  {omega : SixVertexArrows T} :
-- imply
  Fintype.card {v : T.Vertex // omega.IsCType v} = sixVertexTorusCTypeCount omega := by
-- proof
  apply StatMech.FrontierD.card_cTypeSite omega

/--
[card_sixVertexPairCTypeSite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedPairExplicitDecoration.lean)
-/
@[path]
private lemma card_sixVertexPairCTypeSite_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T} :
-- imply
  Fintype.card (SixVertexPairCTypeSite omega eta) = sixVertexTorusCTypeCount omega + sixVertexTorusCTypeCount eta := by
-- proof
  apply StatMech.FrontierD.card_sixVertexPairCTypeSite omega eta

/--
[fkLoopPairingCompatible_of_cType](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedPairExplicitDecoration.lean)
-/
@[path]
private lemma fkLoopPairingCompatible_of_cType_eq
  {T : EvenTorus}
  {omega : SixVertexArrows T}
  {v : T.Vertex}
  {pairing : Bool}
-- given
  (homega : omega.IceRule)
  (hc : omega.IsCType v) :
-- imply
  fkLoopPairingCompatible pairing omega v := by
-- proof
  apply StatMech.FrontierD.fkLoopPairingCompatible_of_cType omega homega v hc pairing

/--
[sixVertexPreferredCompatiblePairing_compatible](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedPairExplicitDecoration.lean)
-/
@[path]
private lemma sixVertexPreferredCompatiblePairing_compatible_eq
  {T : EvenTorus}
  {omega : SixVertexArrows T}
  {v : T.Vertex}
-- given
  (homega : omega.IceRule) :
-- imply
  fkLoopPairingCompatible (sixVertexPreferredCompatiblePairing omega v) omega v := by
-- proof
  apply StatMech.FrontierD.sixVertexPreferredCompatiblePairing_compatible omega homega v

/--
[sixVertexExplicitMarkedPartialPairing_eq_none_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedPairExplicitDecoration.lean)
-/
@[path]
private lemma sixVertexExplicitMarkedPartialPairing_eq_none_iff_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {k : Nat}
  {decoration : SixVertexExplicitMarkedPairDecoration omega eta k}
  {layer : Bool}
  {v : T.Vertex} :
-- imply
  sixVertexExplicitMarkedPartialPairing decoration layer v = none ↔ ∃ site ∈ decoration.1.1, site.1 = (layer, v) := by
-- proof
  apply StatMech.FrontierD.sixVertexExplicitMarkedPartialPairing_eq_none_iff decoration layer v

/--
[mem_sixVertexExplicitMarkedSiteProjection_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedPairExplicitDecoration.lean)
-/
@[path]
private lemma mem_sixVertexExplicitMarkedSiteProjection_iff_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {k : Nat}
  {decoration : SixVertexExplicitMarkedPairDecoration omega eta k}
  {layer : Bool}
  {v : T.Vertex} :
-- imply
  (layer, v) ∈ sixVertexExplicitMarkedSiteProjection decoration ↔ ∃ site ∈ decoration.1.1, site.1 = (layer, v) := by
-- proof
  apply StatMech.FrontierD.mem_sixVertexExplicitMarkedSiteProjection_iff decoration layer v

/--
[sixVertexExplicitUnresolvedSiteFinset_eq_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedPairExplicitDecoration.lean)
-/
@[path]
private lemma sixVertexExplicitUnresolvedSiteFinset_eq_projection_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {k : Nat}
  {decoration : SixVertexExplicitMarkedPairDecoration omega eta k} :
-- imply
  sixVertexExplicitUnresolvedSiteFinset decoration = sixVertexExplicitMarkedSiteProjection decoration := by
-- proof
  apply StatMech.FrontierD.sixVertexExplicitUnresolvedSiteFinset_eq_projection decoration

/--
[card_sixVertexExplicitUnresolvedSiteFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedPairExplicitDecoration.lean)
-/
@[path]
private lemma card_sixVertexExplicitUnresolvedSiteFinset_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {k : Nat}
  {decoration : SixVertexExplicitMarkedPairDecoration omega eta k} :
-- imply
  (sixVertexExplicitUnresolvedSiteFinset decoration).card = k := by
-- proof
  apply StatMech.FrontierD.card_sixVertexExplicitUnresolvedSiteFinset decoration

/--
[card_sixVertexExplicitMarkedResolution](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedPairExplicitDecoration.lean)
-/
@[path]
private lemma card_sixVertexExplicitMarkedResolution_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {k : Nat}
  {decoration : SixVertexExplicitMarkedPairDecoration omega eta k} :
-- imply
  Fintype.card (SixVertexExplicitMarkedResolution decoration) = 2 ^ k := by
-- proof
  apply StatMech.FrontierD.card_sixVertexExplicitMarkedResolution decoration

/--
[sixVertexExplicitResolvedPairing_eq_of_partial_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedPairExplicitDecoration.lean)
-/
@[path]
private lemma sixVertexExplicitResolvedPairing_eq_of_partial_eq_some_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {k : Nat}
  {decoration : SixVertexExplicitMarkedPairDecoration omega eta k}
  {resolution : SixVertexExplicitMarkedResolution decoration}
  {layer : Bool}
  {v : T.Vertex}
  {pairing : Bool}
-- given
  (hpairing : sixVertexExplicitMarkedPartialPairing decoration layer v = some pairing) :
-- imply
  sixVertexExplicitResolvedPairing decoration resolution layer v = pairing := by
-- proof
  apply StatMech.FrontierD.sixVertexExplicitResolvedPairing_eq_of_partial_eq_some decoration resolution layer v pairing hpairing

/--
[sixVertexExplicitResolvedPairing_eq_resolution](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedPairExplicitDecoration.lean)
-/
@[path]
private lemma sixVertexExplicitResolvedPairing_eq_resolution_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {k : Nat}
  {decoration : SixVertexExplicitMarkedPairDecoration omega eta k}
  {resolution : SixVertexExplicitMarkedResolution decoration}
-- given
  (site : {x : Bool × T.Vertex // x ∈ sixVertexExplicitUnresolvedSiteFinset decoration}) :
-- imply
  sixVertexExplicitResolvedPairing decoration resolution site.1.1 site.1.2 = resolution site := by
-- proof
  apply StatMech.FrontierD.sixVertexExplicitResolvedPairing_eq_resolution decoration resolution site

/--
[sixVertexExplicitMarkedPartialPairing_compatible](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedPairExplicitDecoration.lean)
-/
@[path]
private lemma sixVertexExplicitMarkedPartialPairing_compatible_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {k : Nat}
  {decoration : SixVertexExplicitMarkedPairDecoration omega eta k}
  {layer : Bool}
  {v : T.Vertex}
  {pairing : Bool}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hpairing : sixVertexExplicitMarkedPartialPairing decoration layer v = some pairing) :
-- imply
  fkLoopPairingCompatible pairing (sixVertexArrowPairLayer omega eta layer) v := by
-- proof
  apply StatMech.FrontierD.sixVertexExplicitMarkedPartialPairing_compatible homega heta decoration layer v pairing hpairing

/--
[sixVertexExplicitResolvedPairing_compatible](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedPairExplicitDecoration.lean)
-/
@[path]
private lemma sixVertexExplicitResolvedPairing_compatible_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {k : Nat}
  {decoration : SixVertexExplicitMarkedPairDecoration omega eta k}
  {resolution : SixVertexExplicitMarkedResolution decoration}
  {layer : Bool}
  {v : T.Vertex}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule) :
-- imply
  fkLoopPairingCompatible (sixVertexExplicitResolvedPairing decoration resolution layer v) (sixVertexArrowPairLayer omega eta layer) v := by
-- proof
  apply StatMech.FrontierD.sixVertexExplicitResolvedPairing_compatible homega heta decoration resolution layer v

/--
[card_sixVertexExplicitMarkedPairDecoration](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedPairExplicitDecoration.lean)
-/
@[path]
private lemma card_sixVertexExplicitMarkedPairDecoration_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {k : Nat} :
-- imply
  Fintype.card (SixVertexExplicitMarkedPairDecoration omega eta k) = sixVertexMarkedPairMultiplicityNat omega eta k := by
-- proof
  apply StatMech.FrontierD.card_sixVertexExplicitMarkedPairDecoration omega eta k


-- created on 2026-10-23
