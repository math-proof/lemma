import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Onsager.DecorationEdgeClassification
open StatMech StatMech.Onsager


/--
[ons_decGraph_edge_external_or_chain](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationEdgeClassification.lean)
-/
@[path]
private lemma ons_decGraph_edge_external_or_chain_eq
  {L : ℕ}
  [Fact (2 < L)]
  {edge : ons_DecEdge L}
-- given
  (hedge : edge ∈ (ons_decGraph L).edgeFinset) :
-- imply
  (∃ d : ons_Dart L, edge = s(d, ons_dartRev L d)) ∨ ∃ (site : ZMod L × ZMod L) (i : Fin 3), edge = ons_decChainEdge site i := by
-- proof
  apply StatMech.Onsager.ons_decGraph_edge_external_or_chain L edge hedge

/--
[ons_decGraph_edge_isExternal_or_chain](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationEdgeClassification.lean)
-/
@[path]
private lemma ons_decGraph_edge_isExternal_or_chain_eq
  {L : ℕ}
  [Fact (2 < L)]
  {edge : ons_DecEdge L}
-- given
  (hedge : edge ∈ (ons_decGraph L).edgeFinset) :
-- imply
  ons_decIsExternal edge ∨ ∃ (site : ZMod L × ZMod L) (i : Fin 3), edge = ons_decChainEdge site i := by
-- proof
  apply StatMech.Onsager.ons_decGraph_edge_isExternal_or_chain L edge hedge


-- created on 2026-10-23
