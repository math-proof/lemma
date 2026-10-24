import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.HexLiteralHWDepth
open StatMech StatMech.Universality


/--
[hlhc_prefixCoord_eq_endpointPrefixCoord](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean)
-/
@[path]
private lemma hlhc_prefixCoord_eq_endpointPrefixCoord_eq
  {ts : List ℤ}
  {k : ℕ}
-- given
  (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW) :
-- imply
  hlhc_prefixCoord ts hleg.1 k = hexEndpointPrefixCoord ts hleg.1 k := by
-- proof
  apply StatMech.Universality.hlhc_prefixCoord_eq_endpointPrefixCoord ts hleg k

/--
[hlhc_prefixCoord_adjacent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean)
-/
@[path]
private lemma hlhc_prefixCoord_adjacent_eq
  {ts : List ℤ}
  {k : ℕ}
-- given
  (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
  (hk : k < ts.length) :
-- imply
  ∃ e : Fin 3, hexAWNeighbor (hlhc_prefixCoord ts hleg.1 k) e = hlhc_prefixCoord ts hleg.1 (k + 1) := by
-- proof
  apply StatMech.Universality.hlhc_prefixCoord_adjacent ts hleg k hk

/--
[hlhc_prefixCoord_adjacent_legal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean)
-/
@[path]
private lemma hlhc_prefixCoord_adjacent_legal_eq
  {ts : List ℤ}
  {k : ℕ}
-- given
  (hlegal : (ofTurns hexAWStart 1 ts).LegalTurns)
  (hk : k < ts.length) :
-- imply
  ∃ e : Fin 3, hexAWNeighbor (hlhc_prefixCoord ts hlegal k) e = hlhc_prefixCoord ts hlegal (k + 1) := by
-- proof
  apply StatMech.Universality.hlhc_prefixCoord_adjacent_legal ts hlegal k hk

/--
[hlhd_prefix_edge_unit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean)
-/
@[path]
private lemma hlhd_prefix_edge_unit_eq
  {ts : List ℤ}
  {k : ℕ}
  {e : Fin 3}
-- given
  (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
  (hk : k < ts.length)
  (he : hexAWNeighbor (hlhc_prefixCoord ts hleg.1 k) e = hlhc_prefixCoord ts hleg.1 (k + 1)) :
-- imply
  hexUnit (hexInfra_headAccum 1 (ts.take (k + 1))) = hexUnit (hexAWHeading (hlhc_prefixCoord ts hleg.1 k) e) := by
-- proof
  apply StatMech.Universality.hlhd_prefix_edge_unit ts hleg k hk e he

/--
[hlhd_midAccum_prefixEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean)
-/
@[path]
private lemma hlhd_midAccum_prefixEdge_eq
  {ts : List ℤ}
  {k : ℕ}
  {e : Fin 3}
-- given
  (hlegal : (ofTurns hexAWStart 1 ts).LegalTurns)
  (hkpos : 0 < k)
  (hkle : k ≤ ts.length)
  (he : hexAWNeighbor (hlhc_prefixCoord ts hlegal (k - 1)) e = hlhc_prefixCoord ts hlegal k) :
-- imply
  hexInfra_midAccum hexAWStart 1 (ts.take k) = hexAWMid (hlhc_prefixCoord ts hlegal (k - 1)) e := by
-- proof
  apply StatMech.Universality.hlhd_midAccum_prefixEdge ts hlegal k hkpos hkle e he

/--
[hlhc_prefixCoord_append_single](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean)
-/
@[path]
private lemma hlhc_prefixCoord_append_single_eq
  {ts : List ℤ}
  {t : ℤ}
  {k : ℕ}
-- given
  (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
  (hleg' : (ofTurns hexAWStart 1 (ts ++ [t])).IsLegalSAW)
  (hk : k ≤ ts.length) :
-- imply
  hlhc_prefixCoord (ts ++ [t]) hleg'.1 k = hlhc_prefixCoord ts hleg.1 k := by
-- proof
  apply StatMech.Universality.hlhc_prefixCoord_append_single ts hleg t hleg' k hk

/--
[hlhd_neighbor_depth_cases](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean)
-/
@[path]
private lemma hlhd_neighbor_depth_cases_eq
  {c : HexAWCoord}
  {e : Fin 3} :
-- imply
  (hexAWDepth (hexAWNeighbor c e) = hexAWDepth c + 1 ∧ c.color = .black ∧ (e = 1 ∨ e = 2)) ∨ (hexAWDepth (hexAWNeighbor c e) = hexAWDepth c - 1 ∧ c.color = .white ∧ (e = 1 ∨ e = 2)) ∨ (hexAWDepth (hexAWNeighbor c e) = hexAWDepth c ∧ e = 0) := by
-- proof
  apply StatMech.Universality.hlhd_neighbor_depth_cases c e

/--
[hlhd_halfSpace_ahead](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean)
-/
@[path]
private lemma hlhd_halfSpace_ahead_eq
  {ts : List ℤ}
-- given
  (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
  (hhalf : HLHDLiteralHalfSpace ts hleg) :
-- imply
  HLHRAhead (hlhd_height ts hleg) true 0 ts.length := by
-- proof
  apply StatMech.Universality.hlhd_halfSpace_ahead ts hleg hhalf

/--
[hlhd_intervals_reconstruct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean)
-/
@[path]
private lemma hlhd_intervals_reconstruct_eq
  {ts : List ℤ}
-- given
  (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
  (hhalf : HLHDLiteralHalfSpace ts hleg) :
-- imply
  hlhd_intervalTurns ts (hlhd_intervals ts hleg) = ts := by
-- proof
  apply StatMech.Universality.hlhd_intervals_reconstruct ts hleg hhalf

/--
[hlhr_intervalsAux_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean)
-/
@[path]
private lemma hlhr_intervalsAux_bridge_eq
  {f : ℕ → ℝ}
  {up : Bool}
-- given
  (hi fuel lo : ℕ)
  (hlt : lo < hi)
  (hahead : HLHRAhead f up lo hi) :
-- imply
  ∀ p ∈ hlhr_intervalsAux f hi fuel up lo, ∃ dir, HLHRBridgeInterval f dir p := by
-- proof
  apply StatMech.Universality.hlhr_intervalsAux_bridge f hi fuel lo up hlt hahead

/--
[hlhd_interval_is_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean)
-/
@[path]
private lemma hlhd_interval_is_bridge_eq
  {ts : List ℤ}
  {p : ℕ × ℕ}
-- given
  (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
  (hhalf : HLHDLiteralHalfSpace ts hleg)
  (hp : p ∈ hlhd_intervals ts hleg) :
-- imply
  ∃ up, HLHRBridgeInterval (hlhd_height ts hleg) up p := by
-- proof
  apply StatMech.Universality.hlhd_interval_is_bridge ts hleg hhalf p hp

/--
[hlhd_bridge_source_color](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean)
-/
@[path]
private lemma hlhd_bridge_source_color_eq
  {ts : List ℤ}
  {p : ℕ × ℕ}
  {up : Bool}
-- given
  (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
  (hp2 : p.2 ≤ ts.length)
  (hb : HLHRBridgeInterval (hlhd_height ts hleg) up p) :
-- imply
  (up = true ∧ (hlhc_prefixCoord ts hleg.1 p.1).color = .black) ∨ (up = false ∧ (hlhc_prefixCoord ts hleg.1 p.1).color = .white) := by
-- proof
  apply StatMech.Universality.hlhd_bridge_source_color ts hleg p hp2 hb

/--
[hlhd_bridge_depth_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean)
-/
@[path]
private lemma hlhd_bridge_depth_bounds_eq
  {ts : List ℤ}
  {p : ℕ × ℕ}
  {up : Bool}
  {k : ℕ}
-- given
  (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
  (hb : HLHRBridgeInterval (hlhd_height ts hleg) up p)
  (hklo : p.1 ≤ k)
  (hkhi : k ≤ p.2) :
-- imply
  hlhr_signed up (hlhd_height ts hleg p.1) ≤ hlhr_signed up (hlhd_height ts hleg k) ∧ hlhr_signed up (hlhd_height ts hleg k) ≤ hlhr_signed up (hlhd_height ts hleg p.2) := by
-- proof
  apply StatMech.Universality.hlhd_bridge_depth_bounds ts hleg p hb hklo hkhi

/--
[hlhd_interval_index_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean)
-/
@[path]
private lemma hlhd_interval_index_bounds_eq
  {ts : List ℤ}
-- given
  (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
  (hhalf : HLHDLiteralHalfSpace ts hleg) :
-- imply
  ∀ p ∈ hlhd_intervals ts hleg, p.1 < p.2 ∧ p.2 ≤ ts.length := by
-- proof
  apply StatMech.Universality.hlhd_interval_index_bounds ts hleg hhalf

/--
[hlhd_intervalUp_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean)
-/
@[path]
private lemma hlhd_intervalUp_bridge_eq
  {ts : List ℤ}
  {p : ℕ × ℕ}
-- given
  (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
  (hhalf : HLHDLiteralHalfSpace ts hleg)
  (hp : p ∈ hlhd_intervals ts hleg) :
-- imply
  HLHRBridgeInterval (hlhd_height ts hleg) (hlhd_intervalUp ts hleg hhalf p hp) p := by
-- proof
  apply StatMech.Universality.hlhd_intervalUp_bridge ts hleg hhalf p hp

/--
[hlhd_intervalFirstEdge_spec](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean)
-/
@[path]
private lemma hlhd_intervalFirstEdge_spec_eq
  {ts : List ℤ}
  {p : ℕ × ℕ}
-- given
  (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
  (hhalf : HLHDLiteralHalfSpace ts hleg)
  (hp : p ∈ hlhd_intervals ts hleg) :
-- imply
  hexAWNeighbor (hlhc_prefixCoord ts hleg.1 p.1) (hlhd_intervalFirstEdge ts hleg hhalf p hp) = hlhc_prefixCoord ts hleg.1 (p.1 + 1) := by
-- proof
  apply StatMech.Universality.hlhd_intervalFirstEdge_spec ts hleg hhalf p hp

/--
[hlhd_intervalLastEdge_exists](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean)
-/
@[path]
private lemma hlhd_intervalLastEdge_exists_eq
  {ts : List ℤ}
  {p : ℕ × ℕ}
-- given
  (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
  (hhalf : HLHDLiteralHalfSpace ts hleg)
  (hp : p ∈ hlhd_intervals ts hleg) :
-- imply
  ∃ e : Fin 3, hexAWNeighbor (hlhc_prefixCoord ts hleg.1 (p.2 - 1)) e = hlhc_prefixCoord ts hleg.1 p.2 := by
-- proof
  apply StatMech.Universality.hlhd_intervalLastEdge_exists ts hleg hhalf p hp

/--
[hlhd_intervalLastEdge_spec](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean)
-/
@[path]
private lemma hlhd_intervalLastEdge_spec_eq
  {ts : List ℤ}
  {p : ℕ × ℕ}
-- given
  (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
  (hhalf : HLHDLiteralHalfSpace ts hleg)
  (hp : p ∈ hlhd_intervals ts hleg) :
-- imply
  hexAWNeighbor (hlhc_prefixCoord ts hleg.1 (p.2 - 1)) (hlhd_intervalLastEdge ts hleg hhalf p hp) = hlhc_prefixCoord ts hleg.1 p.2 := by
-- proof
  apply StatMech.Universality.hlhd_intervalLastEdge_spec ts hleg hhalf p hp

/--
[hlhd_bridge_first_edge_inward](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean)
-/
@[path]
private lemma hlhd_bridge_first_edge_inward_eq
  {ts : List ℤ}
  {p : ℕ × ℕ}
  {up : Bool}
  {e : Fin 3}
-- given
  (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
  (hb : HLHRBridgeInterval (hlhd_height ts hleg) up p)
  (hp2 : p.2 ≤ ts.length)
  (he : hexAWNeighbor (hlhc_prefixCoord ts hleg.1 p.1) e = hlhc_prefixCoord ts hleg.1 (p.1 + 1)) :
-- imply
  e = 1 ∨ e = 2 := by
-- proof
  apply StatMech.Universality.hlhd_bridge_first_edge_inward ts hleg p hb hp2 e he

/--
[hlhd_intervalFirstEdge_inward](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean)
-/
@[path]
private lemma hlhd_intervalFirstEdge_inward_eq
  {ts : List ℤ}
  {p : ℕ × ℕ}
-- given
  (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
  (hhalf : HLHDLiteralHalfSpace ts hleg)
  (hp : p ∈ hlhd_intervals ts hleg) :
-- imply
  hlhd_intervalFirstEdge ts hleg hhalf p hp = 1 ∨ hlhd_intervalFirstEdge ts hleg hhalf p hp = 2 := by
-- proof
  apply StatMech.Universality.hlhd_intervalFirstEdge_inward ts hleg hhalf p hp

/--
[hlhd_swapColor_invol](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean)
-/
@[path]
private lemma hlhd_swapColor_invol_eq
  {c : HexAWColor} :
-- imply
  hlhd_swapColor (hlhd_swapColor c) = c := by
-- proof
  apply StatMech.Universality.hlhd_swapColor_invol c

/--
[hlhd_normalizeCoord_depth](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean)
-/
@[path]
private lemma hlhd_normalizeCoord_depth_eq
  {up : Bool}
  {source c : HexAWCoord} :
-- imply
  hexAWDepth (hlhd_normalizeCoord up source c) = if up then hexAWDepth c - hexAWDepth source else hexAWDepth source - hexAWDepth c := by
-- proof
  apply StatMech.Universality.hlhd_normalizeCoord_depth up source c

/--
[hlhd_normalizeCoord_neighbor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean)
-/
@[path]
private lemma hlhd_normalizeCoord_neighbor_eq
  {up : Bool}
  {source c : HexAWCoord}
  {e : Fin 3} :
-- imply
  hlhd_normalizeCoord up source (hexAWNeighbor c e) = hexAWNeighbor (hlhd_normalizeCoord up source c) e := by
-- proof
  apply StatMech.Universality.hlhd_normalizeCoord_neighbor up source c e

/--
[hlhd_normalizeCoord_source_up](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean)
-/
@[path]
private lemma hlhd_normalizeCoord_source_up_eq
  {source : HexAWCoord}
-- given
  (hc : source.color = .black) :
-- imply
  hlhd_normalizeCoord true source source = hexAWOriginCoord := by
-- proof
  apply StatMech.Universality.hlhd_normalizeCoord_source_up source hc

/--
[hlhd_normalizeCoord_source_down](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean)
-/
@[path]
private lemma hlhd_normalizeCoord_source_down_eq
  {source : HexAWCoord}
-- given
  (hc : source.color = .white) :
-- imply
  hlhd_normalizeCoord false source source = hexAWOriginCoord := by
-- proof
  apply StatMech.Universality.hlhd_normalizeCoord_source_down source hc

/--
[hlhd_normalizeCoord_heading](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean)
-/
@[path]
private lemma hlhd_normalizeCoord_heading_eq
  {up : Bool}
  {source c : HexAWCoord}
  {e : Fin 3} :
-- imply
  hexAWHeading (hlhd_normalizeCoord up source c) e = if up then hexAWHeading c e else match c.color with := by
-- proof
  apply StatMech.Universality.hlhd_normalizeCoord_heading up source c e

/--
[hlhd_normalizeCoord_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean)
-/
@[path]
private lemma hlhd_normalizeCoord_pos_eq
  {up : Bool}
  {source c : HexAWCoord}
-- given
  (hsource : if up then source.color = .black else source.color = .white) :
-- imply
  hexAWPos (hlhd_normalizeCoord up source c) = if up then hexAWPos c - hexAWPos source else hexAWPos source - hexAWPos c := by
-- proof
  apply StatMech.Universality.hlhd_normalizeCoord_pos up source c hsource

/--
[hlhd_normalizeHeading_true](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean)
-/
@[path]
private lemma hlhd_normalizeHeading_true_eq
-- given
  (h : Fin 6) :
-- imply
  hlhd_normalizeHeading true h = h := by
-- proof
  apply StatMech.Universality.hlhd_normalizeHeading_true h

/--
[hlhd_normalizeHeading_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean)
-/
@[path]
private lemma hlhd_normalizeHeading_false_eq
-- given
  (h : Fin 6) :
-- imply
  hlhd_normalizeHeading false h = h + 3 := by
-- proof
  apply StatMech.Universality.hlhd_normalizeHeading_false h

/--
[hlhd_edgeOfHeading_normalize](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean)
-/
@[path]
private lemma hlhd_edgeOfHeading_normalize_eq
  {up : Bool}
  {source c : HexAWCoord}
-- given
  (h : Fin 6) :
-- imply
  hlhd_edgeOfHeading (hlhd_normalizeCoord up source c) (hlhd_normalizeHeading up h) = hlhd_edgeOfHeading c h := by
-- proof
  apply StatMech.Universality.hlhd_edgeOfHeading_normalize up source c h

/--
[hlhd_normalizeHeading_turn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean)
-/
@[path]
private lemma hlhd_normalizeHeading_turn_eq
  {up : Bool}
  {t : ℤ}
-- given
  (h : Fin 6)
  (ht : t = 1 ∨ t = -1) :
-- imply
  hlhd_normalizeHeading up (hexHeadingTurn h t) = hexHeadingTurn (hlhd_normalizeHeading up h) t := by
-- proof
  apply StatMech.Universality.hlhd_normalizeHeading_turn up h t ht

/--
[hlhd_coordPath_normalize](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean)
-/
@[path]
private lemma hlhd_coordPath_normalize_eq
  {up : Bool}
  {source c : HexAWCoord}
  {ts : List ℤ}
-- given
  (h : Fin 6)
  (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1) :
-- imply
  (hlhd_coordPath c h ts).map (hlhd_normalizeCoord up source) = hlhd_coordPath (hlhd_normalizeCoord up source c) (hlhd_normalizeHeading up h) ts := by
-- proof
  apply StatMech.Universality.hlhd_coordPath_normalize up source c h ts hlegal

/--
[hlhd_interval_source_normalizes](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean)
-/
@[path]
private lemma hlhd_interval_source_normalizes_eq
  {ts : List ℤ}
  {p : ℕ × ℕ}
-- given
  (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
  (hhalf : HLHDLiteralHalfSpace ts hleg)
  (hp : p ∈ hlhd_intervals ts hleg) :
-- imply
  hlhd_normalizeCoord (hlhd_intervalUp ts hleg hhalf p hp) (hlhc_prefixCoord ts hleg.1 p.1) (hlhc_prefixCoord ts hleg.1 p.1) = hexAWOriginCoord := by
-- proof
  apply StatMech.Universality.hlhd_interval_source_normalizes ts hleg hhalf p hp

/--
[hlhd_entryTurn_legal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean)
-/
@[path]
private lemma hlhd_entryTurn_legal_eq
  {e : Fin 3} :
-- imply
  hlhd_entryTurn e = 1 ∨ hlhd_entryTurn e = -1 := by
-- proof
  apply StatMech.Universality.hlhd_entryTurn_legal e

/--
[hlhd_entryTurn_heading](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean)
-/
@[path]
private lemma hlhd_entryTurn_heading_eq
  {e : Fin 3}
-- given
  (he : e = 1 ∨ e = 2) :
-- imply
  1 + hlhd_entryTurn e = hexAWHeading hexAWOriginCoord e := by
-- proof
  apply StatMech.Universality.hlhd_entryTurn_heading he

/--
[hlhd_exitTurn_legal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean)
-/
@[path]
private lemma hlhd_exitTurn_legal_eq
  {e : Fin 3} :
-- imply
  hlhd_exitTurn e = 1 ∨ hlhd_exitTurn e = -1 := by
-- proof
  apply StatMech.Universality.hlhd_exitTurn_legal e

/--
[hlhd_exitTurn_heading](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean)
-/
@[path]
private lemma hlhd_exitTurn_heading_eq
  {e : Fin 3}
-- given
  (he : e = 1 ∨ e = 2) :
-- imply
  hexAWHeading (HexAWCoord.mk 0 0 .black) e + hlhd_exitTurn e = 1 := by
-- proof
  apply StatMech.Universality.hlhd_exitTurn_heading he

/--
[hlhd_columnTag_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean)
-/
@[path]
private lemma hlhd_columnTag_card_eq :
-- imply
  Fintype.card HLHDColumnTag = 8 := by
-- proof
  apply StatMech.Universality.hlhd_columnTag_card

/--
[hlhd_bitTurn_turnBit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean)
-/
@[path]
private lemma hlhd_bitTurn_turnBit_eq
  {t : ℤ}
-- given
  (ht : t = 1 ∨ t = -1) :
-- imply
  hlhd_bitTurn (hlhd_turnBit t) = t := by
-- proof
  apply StatMech.Universality.hlhd_bitTurn_turnBit ht

/--
[hlhd_endpointTurns_length](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean)
-/
@[path]
private lemma hlhd_endpointTurns_length_eq
  {exits : Bool}
  {exitTurn : ℤ}
  {core : List ℤ} :
-- imply
  (hlhd_endpointTurns exits exitTurn core).length = core.length ∨ (hlhd_endpointTurns exits exitTurn core).length = core.length + 1 := by
-- proof
  apply StatMech.Universality.hlhd_endpointTurns_length exits exitTurn core

/--
[hlhd_coreTurns_length](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean)
-/
@[path]
private lemma hlhd_coreTurns_length_eq
  {raw : List ℤ}
  {entry : ℤ}
-- given
  (hraw : raw ≠ []) :
-- imply
  (hlhd_coreTurns entry raw).length = raw.length := by
-- proof
  apply StatMech.Universality.hlhd_coreTurns_length hraw entry

/--
[hlhd_decodeColumn_encode](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean)
-/
@[path]
private lemma hlhd_decodeColumn_encode_eq
  {raw : List ℤ}
  {up exits : Bool}
  {entry exitTurn : ℤ}
-- given
  (hraw : raw ≠ [])
  (hlegal : ∀ t ∈ raw, t = 1 ∨ t = -1) :
-- imply
  hlhd_decodeColumn ⟨up, hlhd_turnBit raw.head!, exits⟩ (hlhd_endpointTurns exits exitTurn (hlhd_coreTurns entry raw)) = raw := by
-- proof
  apply StatMech.Universality.hlhd_decodeColumn_encode hraw hlegal up exits entry exitTurn

/--
[hlhd_raw_eq_of_tagged_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean)
-/
@[path]
private lemma hlhd_raw_eq_of_tagged_eq_eq
  {raw raw' : List ℤ}
  {up up' exits exits' : Bool}
  {entry entry' exitTurn exitTurn' : ℤ}
-- given
  (hraw : raw ≠ [])
  (hraw' : raw' ≠ [])
  (hlegal : ∀ t ∈ raw, t = 1 ∨ t = -1)
  (hlegal' : ∀ t ∈ raw', t = 1 ∨ t = -1)
  (htag : (HLHDColumnTag.mk up (hlhd_turnBit raw.head!) exits) = HLHDColumnTag.mk up' (hlhd_turnBit raw'.head!) exits')
  (hout : hlhd_endpointTurns exits exitTurn (hlhd_coreTurns entry raw) = hlhd_endpointTurns exits' exitTurn' (hlhd_coreTurns entry' raw')) :
-- imply
  raw = raw' := by
-- proof
  apply StatMech.Universality.hlhd_raw_eq_of_tagged_eq hraw hraw' hlegal hlegal' htag hout

/--
[hlhd_interval_legal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean)
-/
@[path]
private lemma hlhd_interval_legal_eq
  {ts : List ℤ}
  {p : ℕ × ℕ}
-- given
  (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
  (hhalf : HLHDLiteralHalfSpace ts hleg)
  (hp : p ∈ hlhd_intervals ts hleg) :
-- imply
  (ofTurns (hlhr_pieceMid hexAWStart 1 ts p.1) (hlhr_pieceHead 1 ts p.1) (hlhr_intervalContent ts p)).IsLegalSAW := by
-- proof
  apply StatMech.Universality.hlhd_interval_legal ts hleg hhalf hp

/--
[hlhd_intervalContent_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean)
-/
@[path]
private lemma hlhd_intervalContent_ne_eq
  {ts : List ℤ}
  {p : ℕ × ℕ}
-- given
  (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
  (hhalf : HLHDLiteralHalfSpace ts hleg)
  (hp : p ∈ hlhd_intervals ts hleg) :
-- imply
  hlhr_intervalContent ts p ≠ [] := by
-- proof
  apply StatMech.Universality.hlhd_intervalContent_ne ts hleg hhalf hp

/--
[hlhd_coreTurns_isLegalSAW](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean)
-/
@[path]
private lemma hlhd_coreTurns_isLegalSAW_eq
  {m : ℂ}
  {h : ℤ}
  {raw : List ℤ}
  {entry : ℤ}
-- given
  (hraw : (ofTurns m h raw).IsLegalSAW)
  (hrawne : raw ≠ [])
  (hentry : entry = 1 ∨ entry = -1) :
-- imply
  (ofTurns hexAWStart 1 (hlhd_coreTurns entry raw)).IsLegalSAW := by
-- proof
  apply StatMech.Universality.hlhd_coreTurns_isLegalSAW hraw hrawne hentry

/--
[hlhd_coreTurns_vertices](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean)
-/
@[path]
private lemma hlhd_coreTurns_vertices_eq
  {raw : List ℤ}
  {entry : ℤ}
-- given
  (hrawne : raw ≠ []) :
-- imply
  verticesAux hexAWStart 1 (hlhd_coreTurns entry raw) = verticesAux (-halfStep (1 + entry - raw.head!)) (1 + entry - raw.head!) raw := by
-- proof
  apply StatMech.Universality.hlhd_coreTurns_vertices hrawne entry

/--
[hlhd_endpointTurns_endpointIsLegalSAW](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean)
-/
@[path]
private lemma hlhd_endpointTurns_endpointIsLegalSAW_eq
  {core : List ℤ}
  {exits : Bool}
  {exitTurn : ℤ}
-- given
  (hcore : (ofTurns hexAWStart 1 core).IsLegalSAW)
  (hexit : exitTurn = 1 ∨ exitTurn = -1) :
-- imply
  (ofTurns hexAWStart 1 (hlhd_endpointTurns exits exitTurn core)).EndpointIsLegalSAW := by
-- proof
  apply StatMech.Universality.hlhd_endpointTurns_endpointIsLegalSAW hcore exits hexit

/--
[hlhd_intervalRaw_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean)
-/
@[path]
private lemma hlhd_intervalRaw_ne_eq
  {ts : List ℤ}
  {p : ℕ × ℕ}
-- given
  (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
  (hhalf : HLHDLiteralHalfSpace ts hleg)
  (hp : p ∈ hlhd_intervals ts hleg) :
-- imply
  hlhd_intervalRaw ts p ≠ [] := by
-- proof
  apply StatMech.Universality.hlhd_intervalRaw_ne ts hleg hhalf p hp

/--
[hlhd_intervalRaw_length](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean)
-/
@[path]
private lemma hlhd_intervalRaw_length_eq
  {ts : List ℤ}
  {p : ℕ × ℕ}
-- given
  (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
  (hhalf : HLHDLiteralHalfSpace ts hleg)
  (hp : p ∈ hlhd_intervals ts hleg) :
-- imply
  (hlhd_intervalRaw ts p).length = p.2 - p.1 := by
-- proof
  apply StatMech.Universality.hlhd_intervalRaw_length ts hleg hhalf p hp

/--
[hlhd_intervalRaw_head_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean)
-/
@[path]
private lemma hlhd_intervalRaw_head_step_eq
  {ts : List ℤ}
  {p : ℕ × ℕ}
-- given
  (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
  (hhalf : HLHDLiteralHalfSpace ts hleg)
  (hp : p ∈ hlhd_intervals ts hleg) :
-- imply
  hexInfra_headAccum 1 (ts.take (p.1 + 1)) = hexInfra_headAccum 1 (ts.take p.1) + (hlhd_intervalRaw ts p).head! := by
-- proof
  apply StatMech.Universality.hlhd_intervalRaw_head_step ts hleg hhalf p hp

/--
[hlhd_interval_entry_unit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean)
-/
@[path]
private lemma hlhd_interval_entry_unit_eq
  {ts : List ℤ}
  {p : ℕ × ℕ}
-- given
  (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
  (hhalf : HLHDLiteralHalfSpace ts hleg)
  (hp : p ∈ hlhd_intervals ts hleg) :
-- imply
  hexUnit (1 + hlhd_entryTurn (hlhd_intervalFirstEdge ts hleg hhalf p hp)) = if hlhd_intervalUp ts hleg hhalf p hp then hexUnit (hexInfra_headAccum 1 (ts.take (p.1 + 1))) else -hexUnit (hexInfra_headAccum 1 (ts.take (p.1 + 1))) := by
-- proof
  apply StatMech.Universality.hlhd_interval_entry_unit ts hleg hhalf p hp

/--
[hlhd_interval_rho](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean)
-/
@[path]
private lemma hlhd_interval_rho_eq
  {ts : List ℤ}
  {p : ℕ × ℕ}
-- given
  (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
  (hhalf : HLHDLiteralHalfSpace ts hleg)
  (hp : p ∈ hlhd_intervals ts hleg) :
-- imply
  let raw := hlhd_intervalRaw ts p let entry := hlhd_entryTurn (hlhd_intervalFirstEdge ts hleg hhalf p hp) let h0 := hexInfra_headAccum 1 (ts.take p.1) let h' := 1 + entry - raw.head! hhe_rho h0 h' = if hlhd_intervalUp ts hleg hhalf p hp then 1 else -1 := by
-- proof
  apply StatMech.Universality.hlhd_interval_rho ts hleg hhalf p hp

/--
[hlhd_intervalCore_vertices_affine](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean)
-/
@[path]
private lemma hlhd_intervalCore_vertices_affine_eq
  {ts : List ℤ}
  {p : ℕ × ℕ}
-- given
  (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
  (hhalf : HLHDLiteralHalfSpace ts hleg)
  (hp : p ∈ hlhd_intervals ts hleg) :
-- imply
  let raw := hlhd_intervalRaw ts p let up := hlhd_intervalUp ts hleg hhalf p hp let source := hlhc_prefixCoord ts hleg.1 p.1 let m0 := hexInfra_midAccum hexAWStart 1 (ts.take p.1) let h0 := hexInfra_headAccum 1 (ts.take p.1) verticesAux hexAWStart 1 (hlhd_intervalCore ts hleg hhalf p hp) = (verticesAux m0 h0 raw).map (fun z => if up then z - hexAWPos source else hexAWPos source - z) := by
-- proof
  apply StatMech.Universality.hlhd_intervalCore_vertices_affine ts hleg hhalf p hp

/--
[hlhd_intervalRaw_vertexPos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean)
-/
@[path]
private lemma hlhd_intervalRaw_vertexPos_eq
  {ts : List ℤ}
  {p : ℕ × ℕ}
  {r : ℕ}
-- given
  (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
  (hhalf : HLHDLiteralHalfSpace ts hleg)
  (hp : p ∈ hlhd_intervals ts hleg)
  (hr : r ≤ (hlhd_intervalRaw ts p).length) :
-- imply
  hexJordan_vertexPos (hexInfra_midAccum hexAWStart 1 (ts.take p.1)) (hexInfra_headAccum 1 (ts.take p.1)) (hlhd_intervalRaw ts p) r = hexJordan_vertexPos hexAWStart 1 ts (p.1 + r) := by
-- proof
  apply StatMech.Universality.hlhd_intervalRaw_vertexPos ts hleg hhalf p hp r hr

/--
[hlhd_intervalRaw_vertices_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean)
-/
@[path]
private lemma hlhd_intervalRaw_vertices_pos_eq
  {ts : List ℤ}
  {p : ℕ × ℕ}
-- given
  (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
  (hhalf : HLHDLiteralHalfSpace ts hleg)
  (hp : p ∈ hlhd_intervals ts hleg) :
-- imply
  verticesAux (hexInfra_midAccum hexAWStart 1 (ts.take p.1)) (hexInfra_headAccum 1 (ts.take p.1)) (hlhd_intervalRaw ts p) = (hlhd_intervalCoords ts hleg p).map hexAWPos := by
-- proof
  apply StatMech.Universality.hlhd_intervalRaw_vertices_pos ts hleg hhalf p hp

/--
[hlhd_intervalNormalizedCoords_length](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean)
-/
@[path]
private lemma hlhd_intervalNormalizedCoords_length_eq
  {ts : List ℤ}
  {p : ℕ × ℕ}
-- given
  (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
  (hhalf : HLHDLiteralHalfSpace ts hleg)
  (hp : p ∈ hlhd_intervals ts hleg) :
-- imply
  (hlhd_intervalNormalizedCoords ts hleg hhalf p hp).length = (hlhd_intervalRaw ts p).length + 1 := by
-- proof
  apply StatMech.Universality.hlhd_intervalNormalizedCoords_length ts hleg hhalf p hp

/--
[hlhd_intervalNormalizedCoords_getElem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean)
-/
@[path]
private lemma hlhd_intervalNormalizedCoords_getElem_eq
  {ts : List ℤ}
  {p : ℕ × ℕ}
  {r : ℕ}
-- given
  (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
  (hhalf : HLHDLiteralHalfSpace ts hleg)
  (hp : p ∈ hlhd_intervals ts hleg)
  (hr : r < (hlhd_intervalNormalizedCoords ts hleg hhalf p hp).length) :
-- imply
  (hlhd_intervalNormalizedCoords ts hleg hhalf p hp)[r] = hlhd_normalizeCoord (hlhd_intervalUp ts hleg hhalf p hp) (hlhc_prefixCoord ts hleg.1 p.1) (hlhc_prefixCoord ts hleg.1 (p.1 + r)) := by
-- proof
  apply StatMech.Universality.hlhd_intervalNormalizedCoords_getElem ts hleg hhalf p hp r hr

/--
[hlhd_intervalCore_vertices_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean)
-/
@[path]
private lemma hlhd_intervalCore_vertices_pos_eq
  {ts : List ℤ}
  {p : ℕ × ℕ}
-- given
  (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
  (hhalf : HLHDLiteralHalfSpace ts hleg)
  (hp : p ∈ hlhd_intervals ts hleg) :
-- imply
  verticesAux hexAWStart 1 (hlhd_intervalCore ts hleg hhalf p hp) = (hlhd_intervalNormalizedCoords ts hleg hhalf p hp).map hexAWPos := by
-- proof
  apply StatMech.Universality.hlhd_intervalCore_vertices_pos ts hleg hhalf p hp

/--
[hlhd_intervalRaw_legal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean)
-/
@[path]
private lemma hlhd_intervalRaw_legal_eq
  {ts : List ℤ}
  {p : ℕ × ℕ}
-- given
  (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
  (hhalf : HLHDLiteralHalfSpace ts hleg)
  (hp : p ∈ hlhd_intervals ts hleg) :
-- imply
  ∀ t ∈ hlhd_intervalRaw ts p, t = 1 ∨ t = -1 := by
-- proof
  apply StatMech.Universality.hlhd_intervalRaw_legal ts hleg hhalf p hp

/--
[hlhd_intervalCore_isLegalSAW](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean)
-/
@[path]
private lemma hlhd_intervalCore_isLegalSAW_eq
  {ts : List ℤ}
  {p : ℕ × ℕ}
-- given
  (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
  (hhalf : HLHDLiteralHalfSpace ts hleg)
  (hp : p ∈ hlhd_intervals ts hleg) :
-- imply
  (ofTurns hexAWStart 1 (hlhd_intervalCore ts hleg hhalf p hp)).IsLegalSAW := by
-- proof
  apply StatMech.Universality.hlhd_intervalCore_isLegalSAW ts hleg hhalf p hp

/--
[hlhd_intervalCore_prefixCoord](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean)
-/
@[path]
private lemma hlhd_intervalCore_prefixCoord_eq
  {ts : List ℤ}
  {p : ℕ × ℕ}
  {r : ℕ}
-- given
  (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
  (hhalf : HLHDLiteralHalfSpace ts hleg)
  (hp : p ∈ hlhd_intervals ts hleg)
  (hr : r ≤ (hlhd_intervalRaw ts p).length) :
-- imply
  hlhc_prefixCoord (hlhd_intervalCore ts hleg hhalf p hp) (hlhd_intervalCore_isLegalSAW ts hleg hhalf p hp).1 r = hlhd_normalizeCoord (hlhd_intervalUp ts hleg hhalf p hp) (hlhc_prefixCoord ts hleg.1 p.1) (hlhc_prefixCoord ts hleg.1 (p.1 + r)) := by
-- proof
  apply StatMech.Universality.hlhd_intervalCore_prefixCoord ts hleg hhalf p hp r hr

/--
[hlhd_endsAt_lastPrefixEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean)
-/
@[path]
private lemma hlhd_endsAt_lastPrefixEdge_eq
  {ws : List ℤ}
  {e : Fin 3}
-- given
  (hws : (ofTurns hexAWStart 1 ws).IsLegalSAW)
  (hne : ws ≠ [])
  (he : hexAWNeighbor (hlhc_prefixCoord ws hws.1 (ws.length - 1)) e = hlhc_prefixCoord ws hws.1 ws.length) :
-- imply
  (ofTurns hexAWStart 1 ws).EndsAt (hexAWMid (hlhc_prefixCoord ws hws.1 (ws.length - 1)) e) := by
-- proof
  apply StatMech.Universality.hlhd_endsAt_lastPrefixEdge ws hws hne e he

/--
[hlhd_neighbor_black_max_edge_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean)
-/
@[path]
private lemma hlhd_neighbor_black_max_edge_zero_eq
  {c d : HexAWCoord}
  {e : Fin 3}
-- given
  (he : hexAWNeighbor c e = d)
  (hd : d.color = .black)
  (hdepth : hexAWDepth c ≤ hexAWDepth d) :
-- imply
  e = 0 := by
-- proof
  apply StatMech.Universality.hlhd_neighbor_black_max_edge_zero c d e he hd hdepth

/--
[hlhd_intervalLastEdge_normalized](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean)
-/
@[path]
private lemma hlhd_intervalLastEdge_normalized_eq
  {ts : List ℤ}
  {p : ℕ × ℕ}
-- given
  (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
  (hhalf : HLHDLiteralHalfSpace ts hleg)
  (hp : p ∈ hlhd_intervals ts hleg) :
-- imply
  hexAWNeighbor (hlhd_intervalPrevCoord ts hleg hhalf p hp) (hlhd_intervalLastEdge ts hleg hhalf p hp) = hlhd_intervalFarCoord ts hleg hhalf p hp := by
-- proof
  apply StatMech.Universality.hlhd_intervalLastEdge_normalized ts hleg hhalf p hp

/--
[hlhd_intervalCore_lastEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean)
-/
@[path]
private lemma hlhd_intervalCore_lastEdge_eq
  {ts : List ℤ}
  {p : ℕ × ℕ}
-- given
  (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
  (hhalf : HLHDLiteralHalfSpace ts hleg)
  (hp : p ∈ hlhd_intervals ts hleg) :
-- imply
  let core := hlhd_intervalCore ts hleg hhalf p hp let hcore := hlhd_intervalCore_isLegalSAW ts hleg hhalf p hp hexAWNeighbor (hlhc_prefixCoord core hcore.1 (core.length - 1)) (hlhd_intervalLastEdge ts hleg hhalf p hp) = hlhc_prefixCoord core hcore.1 core.length := by
-- proof
  apply StatMech.Universality.hlhd_intervalCore_lastEdge ts hleg hhalf p hp

/--
[hlhd_intervalCore_endsAt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean)
-/
@[path]
private lemma hlhd_intervalCore_endsAt_eq
  {ts : List ℤ}
  {p : ℕ × ℕ}
-- given
  (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
  (hhalf : HLHDLiteralHalfSpace ts hleg)
  (hp : p ∈ hlhd_intervals ts hleg) :
-- imply
  (ofTurns hexAWStart 1 (hlhd_intervalCore ts hleg hhalf p hp)).EndsAt (hexAWMid (hlhd_intervalPrevCoord ts hleg hhalf p hp) (hlhd_intervalLastEdge ts hleg hhalf p hp)) := by
-- proof
  apply StatMech.Universality.hlhd_intervalCore_endsAt ts hleg hhalf p hp

/--
[hlhd_intervalEndpoint_endpointIsLegalSAW](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean)
-/
@[path]
private lemma hlhd_intervalEndpoint_endpointIsLegalSAW_eq
  {ts : List ℤ}
  {p : ℕ × ℕ}
-- given
  (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
  (hhalf : HLHDLiteralHalfSpace ts hleg)
  (hp : p ∈ hlhd_intervals ts hleg) :
-- imply
  (ofTurns hexAWStart 1 (hlhd_intervalEndpoint ts hleg hhalf p hp)).EndpointIsLegalSAW := by
-- proof
  apply StatMech.Universality.hlhd_intervalEndpoint_endpointIsLegalSAW ts hleg hhalf p hp

/--
[hlhd_interval_decode](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean)
-/
@[path]
private lemma hlhd_interval_decode_eq
  {ts : List ℤ}
  {p : ℕ × ℕ}
-- given
  (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
  (hhalf : HLHDLiteralHalfSpace ts hleg)
  (hp : p ∈ hlhd_intervals ts hleg) :
-- imply
  hlhd_decodeColumn (hlhd_intervalTag ts hleg hhalf p hp) (hlhd_intervalEndpoint ts hleg hhalf p hp) = hlhd_intervalRaw ts p := by
-- proof
  apply StatMech.Universality.hlhd_interval_decode ts hleg hhalf p hp

/--
[hlhd_intervalEndpoint_length](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean)
-/
@[path]
private lemma hlhd_intervalEndpoint_length_eq
  {ts : List ℤ}
  {p : ℕ × ℕ}
-- given
  (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
  (hhalf : HLHDLiteralHalfSpace ts hleg)
  (hp : p ∈ hlhd_intervals ts hleg) :
-- imply
  (hlhd_intervalEndpoint ts hleg hhalf p hp).length = (hlhd_intervalRaw ts p).length ∨ (hlhd_intervalEndpoint ts hleg hhalf p hp).length = (hlhd_intervalRaw ts p).length + 1 := by
-- proof
  apply StatMech.Universality.hlhd_intervalEndpoint_length ts hleg hhalf p hp

/--
[hlhd_intervalCore_length](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean)
-/
@[path]
private lemma hlhd_intervalCore_length_eq
  {ts : List ℤ}
  {p : ℕ × ℕ}
-- given
  (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
  (hhalf : HLHDLiteralHalfSpace ts hleg)
  (hp : p ∈ hlhd_intervals ts hleg) :
-- imply
  (hlhd_intervalCore ts hleg hhalf p hp).length = (hlhd_intervalRaw ts p).length := by
-- proof
  apply StatMech.Universality.hlhd_intervalCore_length ts hleg hhalf p hp

/--
[hlhd_intervalEndpoint_index_le_core](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean)
-/
@[path]
private lemma hlhd_intervalEndpoint_index_le_core_eq
  {ts : List ℤ}
  {p : ℕ × ℕ}
  {k : ℕ}
-- given
  (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
  (hhalf : HLHDLiteralHalfSpace ts hleg)
  (hp : p ∈ hlhd_intervals ts hleg)
  (hk : k < (hlhd_intervalEndpoint ts hleg hhalf p hp).length) :
-- imply
  k ≤ (hlhd_intervalCore ts hleg hhalf p hp).length := by
-- proof
  apply StatMech.Universality.hlhd_intervalEndpoint_index_le_core ts hleg hhalf p hp hk

/--
[hlhd_intervalEndpoint_prefixCoord_eq_core](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean)
-/
@[path]
private lemma hlhd_intervalEndpoint_prefixCoord_eq_core_eq
  {ts : List ℤ}
  {p : ℕ × ℕ}
  {k : ℕ}
-- given
  (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
  (hhalf : HLHDLiteralHalfSpace ts hleg)
  (hp : p ∈ hlhd_intervals ts hleg)
  (hk : k ≤ (hlhd_intervalCore ts hleg hhalf p hp).length) :
-- imply
  hlhc_prefixCoord (hlhd_intervalEndpoint ts hleg hhalf p hp) (hlhd_intervalEndpoint_endpointIsLegalSAW ts hleg hhalf p hp).1 k = hlhc_prefixCoord (hlhd_intervalCore ts hleg hhalf p hp) (hlhd_intervalCore_isLegalSAW ts hleg hhalf p hp).1 k := by
-- proof
  apply StatMech.Universality.hlhd_intervalEndpoint_prefixCoord_eq_core ts hleg hhalf p hp k hk

/--
[hlhd_spans_pairwise](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean)
-/
@[path]
private lemma hlhd_spans_pairwise_eq
  {ts : List ℤ}
-- given
  (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
  (hhalf : HLHDLiteralHalfSpace ts hleg) :
-- imply
  (hlhd_spans ts hleg).Pairwise (· > ·) := by
-- proof
  apply StatMech.Universality.hlhd_spans_pairwise ts hleg hhalf

/--
[hlhd_spans_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean)
-/
@[path]
private lemma hlhd_spans_pos_eq
  {ts : List ℤ}
-- given
  (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
  (hhalf : HLHDLiteralHalfSpace ts hleg) :
-- imply
  ∀ w ∈ hlhd_spans ts hleg, 0 < w := by
-- proof
  apply StatMech.Universality.hlhd_spans_pos ts hleg hhalf

/--
[hlhd_normalized_depth_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean)
-/
@[path]
private lemma hlhd_normalized_depth_bounds_eq
  {ts : List ℤ}
  {p : ℕ × ℕ}
  {up : Bool}
  {k : ℕ}
-- given
  (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
  (hb : HLHRBridgeInterval (hlhd_height ts hleg) up p)
  (hklo : p.1 ≤ k)
  (hkhi : k ≤ p.2) :
-- imply
  0 ≤ hexAWDepth (hlhd_normalizeCoord up (hlhc_prefixCoord ts hleg.1 p.1) (hlhc_prefixCoord ts hleg.1 k)) ∧ hexAWDepth (hlhd_normalizeCoord up (hlhc_prefixCoord ts hleg.1 p.1) (hlhc_prefixCoord ts hleg.1 k)) ≤ (hlhd_width ts hleg p : ℤ) := by
-- proof
  apply StatMech.Universality.hlhd_normalized_depth_bounds ts hleg p hb hklo hkhi

/--
[hlhd_normalized_depth_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean)
-/
@[path]
private lemma hlhd_normalized_depth_pos_eq
  {ts : List ℤ}
  {p : ℕ × ℕ}
  {up : Bool}
  {k : ℕ}
-- given
  (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
  (hb : HLHRBridgeInterval (hlhd_height ts hleg) up p)
  (hklo : p.1 < k)
  (hkhi : k ≤ p.2) :
-- imply
  0 < hexAWDepth (hlhd_normalizeCoord up (hlhc_prefixCoord ts hleg.1 p.1) (hlhc_prefixCoord ts hleg.1 k)) := by
-- proof
  apply StatMech.Universality.hlhd_normalized_depth_pos ts hleg p hb hklo hkhi

/--
[hlhd_normalized_endpoint_depth](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean)
-/
@[path]
private lemma hlhd_normalized_endpoint_depth_eq
  {ts : List ℤ}
  {p : ℕ × ℕ}
  {up : Bool}
-- given
  (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
  (hb : HLHRBridgeInterval (hlhd_height ts hleg) up p) :
-- imply
  hexAWDepth (hlhd_normalizeCoord up (hlhc_prefixCoord ts hleg.1 p.1) (hlhc_prefixCoord ts hleg.1 p.2)) = hlhd_width ts hleg p := by
-- proof
  apply StatMech.Universality.hlhd_normalized_endpoint_depth ts hleg p hb

/--
[hlhd_intervalFarCoord_depth](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean)
-/
@[path]
private lemma hlhd_intervalFarCoord_depth_eq
  {ts : List ℤ}
  {p : ℕ × ℕ}
-- given
  (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
  (hhalf : HLHDLiteralHalfSpace ts hleg)
  (hp : p ∈ hlhd_intervals ts hleg) :
-- imply
  hexAWDepth (hlhd_intervalFarCoord ts hleg hhalf p hp) = hlhd_width ts hleg p := by
-- proof
  apply StatMech.Universality.hlhd_intervalFarCoord_depth ts hleg hhalf p hp

/--
[hlhd_intervalPrevCoord_depth_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean)
-/
@[path]
private lemma hlhd_intervalPrevCoord_depth_le_eq
  {ts : List ℤ}
  {p : ℕ × ℕ}
-- given
  (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
  (hhalf : HLHDLiteralHalfSpace ts hleg)
  (hp : p ∈ hlhd_intervals ts hleg) :
-- imply
  hexAWDepth (hlhd_intervalPrevCoord ts hleg hhalf p hp) ≤ hexAWDepth (hlhd_intervalFarCoord ts hleg hhalf p hp) := by
-- proof
  apply StatMech.Universality.hlhd_intervalPrevCoord_depth_le ts hleg hhalf p hp

/--
[hlhd_intervalLastEdge_zero_of_far_black](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean)
-/
@[path]
private lemma hlhd_intervalLastEdge_zero_of_far_black_eq
  {ts : List ℤ}
  {p : ℕ × ℕ}
-- given
  (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
  (hhalf : HLHDLiteralHalfSpace ts hleg)
  (hp : p ∈ hlhd_intervals ts hleg)
  (hblack : (hlhd_intervalFarCoord ts hleg hhalf p hp).color = .black) :
-- imply
  hlhd_intervalLastEdge ts hleg hhalf p hp = 0 := by
-- proof
  apply StatMech.Universality.hlhd_intervalLastEdge_zero_of_far_black ts hleg hhalf p hp hblack

/--
[hlhd_intervalTopCoord_white](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean)
-/
@[path]
private lemma hlhd_intervalTopCoord_white_eq
  {ts : List ℤ}
  {p : ℕ × ℕ}
-- given
  (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
  (hhalf : HLHDLiteralHalfSpace ts hleg)
  (hp : p ∈ hlhd_intervals ts hleg) :
-- imply
  (hlhd_intervalTopCoord ts hleg hhalf p hp).color = .white := by
-- proof
  apply StatMech.Universality.hlhd_intervalTopCoord_white ts hleg hhalf p hp

/--
[hlhd_neighbor_zero_depth](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean)
-/
@[path]
private lemma hlhd_neighbor_zero_depth_eq
  {c : HexAWCoord} :
-- imply
  hexAWDepth (hexAWNeighbor c 0) = hexAWDepth c := by
-- proof
  apply StatMech.Universality.hlhd_neighbor_zero_depth c

/--
[hlhd_intervalTopCoord_depth](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean)
-/
@[path]
private lemma hlhd_intervalTopCoord_depth_eq
  {ts : List ℤ}
  {p : ℕ × ℕ}
-- given
  (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
  (hhalf : HLHDLiteralHalfSpace ts hleg)
  (hp : p ∈ hlhd_intervals ts hleg) :
-- imply
  hexAWDepth (hlhd_intervalTopCoord ts hleg hhalf p hp) = hlhd_width ts hleg p := by
-- proof
  apply StatMech.Universality.hlhd_intervalTopCoord_depth ts hleg hhalf p hp

/--
[hlhd_intervalExits_false_of_far_black](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean)
-/
@[path]
private lemma hlhd_intervalExits_false_of_far_black_eq
  {ts : List ℤ}
  {p : ℕ × ℕ}
-- given
  (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
  (hhalf : HLHDLiteralHalfSpace ts hleg)
  (hp : p ∈ hlhd_intervals ts hleg)
  (hblack : (hlhd_intervalFarCoord ts hleg hhalf p hp).color = .black) :
-- imply
  hlhd_intervalExits ts hleg hhalf p hp = false := by
-- proof
  apply StatMech.Universality.hlhd_intervalExits_false_of_far_black ts hleg hhalf p hp hblack

/--
[hlhd_intervalFarCoord_white_of_exits](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean)
-/
@[path]
private lemma hlhd_intervalFarCoord_white_of_exits_eq
  {ts : List ℤ}
  {p : ℕ × ℕ}
-- given
  (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
  (hhalf : HLHDLiteralHalfSpace ts hleg)
  (hp : p ∈ hlhd_intervals ts hleg)
  (hexits : hlhd_intervalExits ts hleg hhalf p hp = true) :
-- imply
  (hlhd_intervalFarCoord ts hleg hhalf p hp).color = .white := by
-- proof
  apply StatMech.Universality.hlhd_intervalFarCoord_white_of_exits ts hleg hhalf p hp hexits

/--
[hlhd_hexUnit_add_eq_of_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean)
-/
@[path]
private lemma hlhd_hexUnit_add_eq_of_eq_eq
-- given
  (h k t : ℤ)
  (hu : hexUnit h = hexUnit k) :
-- imply
  hexUnit (h + t) = hexUnit (k + t) := by
-- proof
  apply StatMech.Universality.hlhd_hexUnit_add_eq_of_eq h k t hu

/--
[hlhd_exit_heading_unit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean)
-/
@[path]
private lemma hlhd_exit_heading_unit_eq
  {c d : HexAWCoord}
  {e : Fin 3}
-- given
  (he : hexAWNeighbor c e = d)
  (hd : d.color = .white)
  (hin : e = 1 ∨ e = 2) :
-- imply
  hexUnit (hexAWHeading c e + hlhd_exitTurn e) = hexUnit (hexAWHeading d 0) := by
-- proof
  apply StatMech.Universality.hlhd_exit_heading_unit c d e he hd hin

/--
[hlhd_append_exit_endsAt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean)
-/
@[path]
private lemma hlhd_append_exit_endsAt_eq
  {ws : List ℤ}
  {c d : HexAWCoord}
  {e : Fin 3}
-- given
  (hend : (ofTurns hexAWStart 1 ws).EndsAt (hexAWMid c e))
  (hhead : hexUnit (hexInfra_headAccum 1 ws) = hexUnit (hexAWHeading c e))
  (he : hexAWNeighbor c e = d)
  (hd : d.color = .white)
  (hin : e = 1 ∨ e = 2) :
-- imply
  (ofTurns hexAWStart 1 (ws ++ [hlhd_exitTurn e])).EndsAt (hexAWMid d 0) := by
-- proof
  apply StatMech.Universality.hlhd_append_exit_endsAt ws c d e hend hhead he hd hin

/--
[hlhd_intervalCore_finalCoord](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean)
-/
@[path]
private lemma hlhd_intervalCore_finalCoord_eq
  {ts : List ℤ}
  {p : ℕ × ℕ}
-- given
  (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
  (hhalf : HLHDLiteralHalfSpace ts hleg)
  (hp : p ∈ hlhd_intervals ts hleg) :
-- imply
  let core := hlhd_intervalCore ts hleg hhalf p hp let hcore := hlhd_intervalCore_isLegalSAW ts hleg hhalf p hp hlhc_prefixCoord core hcore.1 core.length = hlhd_intervalFarCoord ts hleg hhalf p hp := by
-- proof
  apply StatMech.Universality.hlhd_intervalCore_finalCoord ts hleg hhalf p hp

/--
[hlhd_intervalCore_prevCoord](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean)
-/
@[path]
private lemma hlhd_intervalCore_prevCoord_eq
  {ts : List ℤ}
  {p : ℕ × ℕ}
-- given
  (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
  (hhalf : HLHDLiteralHalfSpace ts hleg)
  (hp : p ∈ hlhd_intervals ts hleg) :
-- imply
  let core := hlhd_intervalCore ts hleg hhalf p hp let hcore := hlhd_intervalCore_isLegalSAW ts hleg hhalf p hp hlhc_prefixCoord core hcore.1 (core.length - 1) = hlhd_intervalPrevCoord ts hleg hhalf p hp := by
-- proof
  apply StatMech.Universality.hlhd_intervalCore_prevCoord ts hleg hhalf p hp

/--
[hlhd_intervalCore_heading_unit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean)
-/
@[path]
private lemma hlhd_intervalCore_heading_unit_eq
  {ts : List ℤ}
  {p : ℕ × ℕ}
-- given
  (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
  (hhalf : HLHDLiteralHalfSpace ts hleg)
  (hp : p ∈ hlhd_intervals ts hleg) :
-- imply
  hexUnit (hexInfra_headAccum 1 (hlhd_intervalCore ts hleg hhalf p hp)) = hexUnit (hexAWHeading (hlhd_intervalPrevCoord ts hleg hhalf p hp) (hlhd_intervalLastEdge ts hleg hhalf p hp)) := by
-- proof
  apply StatMech.Universality.hlhd_intervalCore_heading_unit ts hleg hhalf p hp

/--
[hlhd_fin3_inward_of_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean)
-/
@[path]
private lemma hlhd_fin3_inward_of_ne_zero_eq
  {e : Fin 3}
-- given
  (he : e ≠ 0) :
-- imply
  e = 1 ∨ e = 2 := by
-- proof
  apply StatMech.Universality.hlhd_fin3_inward_of_ne_zero e he

/--
[hlhd_fin3_zero_of_decide_ne_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean)
-/
@[path]
private lemma hlhd_fin3_zero_of_decide_ne_false_eq
  {e : Fin 3}
-- given
  (he : decide (e ≠ 0) = false) :
-- imply
  e = 0 := by
-- proof
  apply StatMech.Universality.hlhd_fin3_zero_of_decide_ne_false e he

/--
[hlhd_intervalCore_endsAt_top_of_noExit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean)
-/
@[path]
private lemma hlhd_intervalCore_endsAt_top_of_noExit_eq
  {ts : List ℤ}
  {p : ℕ × ℕ}
-- given
  (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
  (hhalf : HLHDLiteralHalfSpace ts hleg)
  (hp : p ∈ hlhd_intervals ts hleg)
  (hexits : hlhd_intervalExits ts hleg hhalf p hp = false) :
-- imply
  (ofTurns hexAWStart 1 (hlhd_intervalCore ts hleg hhalf p hp)).EndsAt (hexAWMid (hlhd_intervalTopCoord ts hleg hhalf p hp) 0) := by
-- proof
  apply StatMech.Universality.hlhd_intervalCore_endsAt_top_of_noExit ts hleg hhalf p hp hexits

/--
[hlhd_intervalEndpoint_endsAt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean)
-/
@[path]
private lemma hlhd_intervalEndpoint_endsAt_eq
  {ts : List ℤ}
  {p : ℕ × ℕ}
-- given
  (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
  (hhalf : HLHDLiteralHalfSpace ts hleg)
  (hp : p ∈ hlhd_intervals ts hleg) :
-- imply
  (ofTurns hexAWStart 1 (hlhd_intervalEndpoint ts hleg hhalf p hp)).EndsAt (hexAWMid (hlhd_intervalTopCoord ts hleg hhalf p hp) 0) := by
-- proof
  apply StatMech.Universality.hlhd_intervalEndpoint_endsAt ts hleg hhalf p hp

/--
[hlhd_intervalCore_depth_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean)
-/
@[path]
private lemma hlhd_intervalCore_depth_bounds_eq
  {ts : List ℤ}
  {p : ℕ × ℕ}
  {r : ℕ}
-- given
  (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
  (hhalf : HLHDLiteralHalfSpace ts hleg)
  (hp : p ∈ hlhd_intervals ts hleg)
  (hr : r ≤ (hlhd_intervalCore ts hleg hhalf p hp).length) :
-- imply
  0 ≤ hexAWDepth (hlhc_prefixCoord (hlhd_intervalCore ts hleg hhalf p hp) (hlhd_intervalCore_isLegalSAW ts hleg hhalf p hp).1 r) ∧ hexAWDepth (hlhc_prefixCoord (hlhd_intervalCore ts hleg hhalf p hp) (hlhd_intervalCore_isLegalSAW ts hleg hhalf p hp).1 r) ≤ (hlhd_width ts hleg p : ℤ) := by
-- proof
  apply StatMech.Universality.hlhd_intervalCore_depth_bounds ts hleg hhalf p hp r hr

/--
[hlhd_intervalCore_white_depth_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean)
-/
@[path]
private lemma hlhd_intervalCore_white_depth_pos_eq
  {ts : List ℤ}
  {p : ℕ × ℕ}
  {r : ℕ}
-- given
  (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
  (hhalf : HLHDLiteralHalfSpace ts hleg)
  (hp : p ∈ hlhd_intervals ts hleg)
  (hr : r ≤ (hlhd_intervalCore ts hleg hhalf p hp).length)
  (hwhite : (hlhc_prefixCoord (hlhd_intervalCore ts hleg hhalf p hp) (hlhd_intervalCore_isLegalSAW ts hleg hhalf p hp).1 r).color = .white) :
-- imply
  0 < hexAWDepth (hlhc_prefixCoord (hlhd_intervalCore ts hleg hhalf p hp) (hlhd_intervalCore_isLegalSAW ts hleg hhalf p hp).1 r) := by
-- proof
  apply StatMech.Universality.hlhd_intervalCore_white_depth_pos ts hleg hhalf p hp r hr hwhite

/--
[hlhd_white_depth_mem_horizontal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean)
-/
@[path]
private lemma hlhd_white_depth_mem_horizontal_eq
  {T : ℕ}
  {c : HexAWCoord}
-- given
  (hwhite : c.color = .white)
  (hpos : 0 < hexAWDepth c)
  (hupper : hexAWDepth c ≤ T) :
-- imply
  0 ≤ hexAWBookRe2 c ∧ hexAWBookRe2 c ≤ 3 * T := by
-- proof
  apply StatMech.Universality.hlhd_white_depth_mem_horizontal T c hwhite hpos hupper

/--
[hlhd_span_eq_width](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean)
-/
@[path]
private lemma hlhd_span_eq_width_eq
  {ts : List ℤ}
  {p : ℕ × ℕ}
-- given
  (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW) :
-- imply
  hlhr_intervalSpan (hlhd_height ts hleg) p = hlhd_width ts hleg p := by
-- proof
  apply StatMech.Universality.hlhd_span_eq_width ts hleg p

/--
[hlhd_width_pos_of_span_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean)
-/
@[path]
private lemma hlhd_width_pos_of_span_pos_eq
  {ts : List ℤ}
  {p : ℕ × ℕ}
-- given
  (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
  (hp : 0 < hlhr_intervalSpan (hlhd_height ts hleg) p) :
-- imply
  0 < hlhd_width ts hleg p := by
-- proof
  apply StatMech.Universality.hlhd_width_pos_of_span_pos ts hleg p hp

/--
[hlhd_width_gt_of_span_gt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean)
-/
@[path]
private lemma hlhd_width_gt_of_span_gt_eq
  {ts : List ℤ}
  {p q : ℕ × ℕ}
-- given
  (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
  (hpq : hlhr_intervalSpan (hlhd_height ts hleg) p > hlhr_intervalSpan (hlhd_height ts hleg) q) :
-- imply
  hlhd_width ts hleg p > hlhd_width ts hleg q := by
-- proof
  apply StatMech.Universality.hlhd_width_gt_of_span_gt ts hleg p q hpq

/--
[hlhd_interval_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean)
-/
@[path]
private lemma hlhd_interval_bounds_eq
  {ts : List ℤ}
-- given
  (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
  (hhalf : HLHDLiteralHalfSpace ts hleg) :
-- imply
  ∀ p ∈ hlhd_intervals ts hleg, p.1 < p.2 ∧ p.2 ≤ ts.length := by
-- proof
  apply StatMech.Universality.hlhd_interval_bounds ts hleg hhalf

/--
[hlhd_bridgeList_widths](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean)
-/
@[path]
private lemma hlhd_bridgeList_widths_eq
  {ts : List ℤ}
-- given
  (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
  (hhalf : HLHDLiteralHalfSpace ts hleg) :
-- imply
  (hlhd_bridgeList ts hleg hhalf).map HexBridge.width = (hlhd_intervals ts hleg).map (hlhd_width ts hleg) := by
-- proof
  apply StatMech.Universality.hlhd_bridgeList_widths ts hleg hhalf

/--
[hlhd_bridgeList_contents](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean)
-/
@[path]
private lemma hlhd_bridgeList_contents_eq
  {ts : List ℤ}
-- given
  (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
  (hhalf : HLHDLiteralHalfSpace ts hleg) :
-- imply
  ((hlhd_bridgeList ts hleg hhalf).map HexBridge.content).flatten = ts := by
-- proof
  apply StatMech.Universality.hlhd_bridgeList_contents ts hleg hhalf

/--
[hlhd_bridgeList_strict](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean)
-/
@[path]
private lemma hlhd_bridgeList_strict_eq
  {ts : List ℤ}
-- given
  (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
  (hhalf : HLHDLiteralHalfSpace ts hleg) :
-- imply
  StrictDecreasingWidths (hlhd_bridgeList ts hleg hhalf) := by
-- proof
  apply StatMech.Universality.hlhd_bridgeList_strict ts hleg hhalf

/--
[hlhd_contentHalf_turns](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean)
-/
@[path]
private lemma hlhd_contentHalf_turns_eq
  {ts : List ℤ}
-- given
  (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
  (hhalf : HLHDLiteralHalfSpace ts hleg) :
-- imply
  hhc_halfTurns (hlhd_contentHalf ts hleg hhalf) = ts := by
-- proof
  apply StatMech.Universality.hlhd_contentHalf_turns ts hleg hhalf

/--
[hlhd_interval_width_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean)
-/
@[path]
private lemma hlhd_interval_width_pos_eq
  {ts : List ℤ}
  {p : ℕ × ℕ}
-- given
  (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
  (hhalf : HLHDLiteralHalfSpace ts hleg)
  (hp : p ∈ hlhd_intervals ts hleg) :
-- imply
  0 < hlhd_width ts hleg p := by
-- proof
  apply StatMech.Universality.hlhd_interval_width_pos ts hleg hhalf p hp

/--
[hlhd_neighbor_white_of_black](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean)
-/
@[path]
private lemma hlhd_neighbor_white_of_black_eq
  {c d : HexAWCoord}
  {e : Fin 3}
-- given
  (hc : c.color = .black)
  (he : hexAWNeighbor c e = d) :
-- imply
  d.color = .white := by
-- proof
  apply StatMech.Universality.hlhd_neighbor_white_of_black hc he

/--
[hlhd_intervalEndpoint_mid_incident_horizontal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean)
-/
@[path]
private lemma hlhd_intervalEndpoint_mid_incident_horizontal_eq
  {ts : List ℤ}
  {p : ℕ × ℕ}
  {k : ℕ}
-- given
  (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
  (hhalf : HLHDLiteralHalfSpace ts hleg)
  (hp : p ∈ hlhd_intervals ts hleg)
  (hk : k < (hlhd_intervalEndpoint ts hleg hhalf p hp).length) :
-- imply
  ∃ c : HexAWCoord, ∃ e : Fin 3, hexInfra_midAccum hexAWStart 1 ((hlhd_intervalEndpoint ts hleg hhalf p hp).take k) = hexAWMid c e ∧ 0 ≤ hexAWBookRe2 c ∧ hexAWBookRe2 c ≤ 3 * hlhd_width ts hleg p := by
-- proof
  apply StatMech.Universality.hlhd_intervalEndpoint_mid_incident_horizontal ts hleg hhalf p hp k hk

/--
[hlhd_intervalMid_spec](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean)
-/
@[path]
private lemma hlhd_intervalMid_spec_eq
  {ts : List ℤ}
  {p : ℕ × ℕ}
  {k : Fin (hlhd_intervalEndpoint ts hleg hhalf p hp).length}
-- given
  (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
  (hhalf : HLHDLiteralHalfSpace ts hleg)
  (hp : p ∈ hlhd_intervals ts hleg) :
-- imply
  hexInfra_midAccum hexAWStart 1 ((hlhd_intervalEndpoint ts hleg hhalf p hp).take k.1) = hexAWMid (hlhd_intervalMidCoord ts hleg hhalf p hp k) (hlhd_intervalMidEdge ts hleg hhalf p hp k) ∧ 0 ≤ hexAWBookRe2 (hlhd_intervalMidCoord ts hleg hhalf p hp k) ∧ hexAWBookRe2 (hlhd_intervalMidCoord ts hleg hhalf p hp k) ≤ 3 * hlhd_width ts hleg p := by
-- proof
  apply StatMech.Universality.hlhd_intervalMid_spec ts hleg hhalf p hp k

/--
[hlhd_intervalEndpoint_mem_topAtWidth](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean)
-/
@[path]
private lemma hlhd_intervalEndpoint_mem_topAtWidth_eq
  {ts : List ℤ}
  {p : ℕ × ℕ}
-- given
  (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
  (hhalf : HLHDLiteralHalfSpace ts hleg)
  (hp : p ∈ hlhd_intervals ts hleg) :
-- imply
  HexCSTopWalkAtWidth (hlhd_width ts hleg p) (hlhd_interval_width_pos ts hleg hhalf p hp) (hlhd_intervalEndpoint ts hleg hhalf p hp) := by
-- proof
  apply StatMech.Universality.hlhd_intervalEndpoint_mem_topAtWidth ts hleg hhalf p hp


-- created on 2026-10-23
