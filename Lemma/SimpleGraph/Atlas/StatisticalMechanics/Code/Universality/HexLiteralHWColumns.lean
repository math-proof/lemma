import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.HexLiteralHWColumns
open StatMech StatMech.Universality


/--
[hlhr_stripColumnRealization_zero_column](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWColumns.lean)
-/
@[path]
private lemma hlhr_stripColumnRealization_zero_column_eq
  {ts : List ℤ}
  {p : ℕ × ℕ}
-- given
  (hleg : (ofTurns 0 0 ts).IsLegalSAW)
  (hhalf : HLHRLiteralHalfSpace 0 ts)
  (hp : p ∈ hlhr_literalIntervals 0 ts) :
-- imply
  (hlhr_stripColumnRealization_zero ts hleg hhalf).column p hp = hlhr_latticeWidth ts p := by
-- proof
  apply StatMech.Universality.hlhr_stripColumnRealization_zero_column ts hleg hhalf p hp

/--
[hlhr_literalBridge_mem_with_column](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWColumns.lean)
-/
@[path]
private lemma hlhr_literalBridge_mem_with_column_eq
  {ts : List ℤ}
  {b : HexBridge}
-- given
  (hleg : (ofTurns 0 0 ts).IsLegalSAW)
  (hhalf : HLHRLiteralHalfSpace 0 ts)
  (hb : b ∈ hlhr_literalBridgeList ts hleg hhalf) :
-- imply
  ∃ p : {p // p ∈ hlhr_literalIntervals 0 ts}, b = hlhr_literalBridge ts hleg hhalf p ∧ b.width = (hlhr_stripColumnRealization_zero ts hleg hhalf).column p.1 p.2 := by
-- proof
  apply StatMech.Universality.hlhr_literalBridge_mem_with_column ts hleg hhalf b hb

/--
[hlhc_coord_le_bound_i](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWColumns.lean)
-/
@[path]
private lemma hlhc_coord_le_bound_i_eq
  {c : HexAWCoord} :
-- imply
  c.i ≤ (hlhc_coordBound c : ℕ) := by
-- proof
  apply StatMech.Universality.hlhc_coord_le_bound_i c

/--
[hlhc_coord_le_bound_j](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWColumns.lean)
-/
@[path]
private lemma hlhc_coord_le_bound_j_eq
  {c : HexAWCoord} :
-- imply
  c.j ≤ (hlhc_coordBound c : ℕ) := by
-- proof
  apply StatMech.Universality.hlhc_coord_le_bound_j c

/--
[hlhc_prefixCoord_vertex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWColumns.lean)
-/
@[path]
private lemma hlhc_prefixCoord_vertex_eq
  {ts : List ℤ}
  {k : ℕ}
-- given
  (hlegal : (ofTurns hexAWStart 1 ts).LegalTurns) :
-- imply
  hexInfra_midAccum hexAWStart 1 (ts.take k) + halfStep (hexInfra_headAccum 1 (ts.take k)) = hexAWPos (hlhc_prefixCoord ts hlegal k) := by
-- proof
  apply StatMech.Universality.hlhc_prefixCoord_vertex ts hlegal k

/--
[hlhc_prefixCoord_mid_incident](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWColumns.lean)
-/
@[path]
private lemma hlhc_prefixCoord_mid_incident_eq
  {ts : List ℤ}
  {k : ℕ}
-- given
  (hlegal : (ofTurns hexAWStart 1 ts).LegalTurns) :
-- imply
  ∃ e : Fin 3, hexInfra_midAccum hexAWStart 1 (ts.take k) = hexAWMid (hlhc_prefixCoord ts hlegal k) e := by
-- proof
  apply StatMech.Universality.hlhc_prefixCoord_mid_incident ts hlegal k

/--
[HLHCCanonicalColumnWalk.prefix_mem_vertexSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWColumns.lean)
-/
@[path]
private lemma prefix_mem_vertexSet_eq
  {T : ℕ}
  {ts : List ℤ}
  {W : HLHCCanonicalColumnWalk T ts}
  {k : ℕ}
-- given
  (hk : k < ts.length) :
-- imply
  hlhc_prefixCoord ts W.legal.1 k ∈ hexCSVertexSet T W.stripHeight := by
-- proof
  apply StatMech.Universality.HLHCCanonicalColumnWalk.prefix_mem_vertexSet W hk

/--
[HLHCCanonicalColumnWalk.top_mem_vertexSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWColumns.lean)
-/
@[path]
private lemma top_mem_vertexSet_eq
  {T : ℕ}
  {ts : List ℤ}
  {W : HLHCCanonicalColumnWalk T ts}
-- given
  (hT : 0 < T) :
-- imply
  W.topCoord ∈ hexCSVertexSet T W.stripHeight := by
-- proof
  apply StatMech.Universality.HLHCCanonicalColumnWalk.top_mem_vertexSet W hT

/--
[HexWalk.IsLegalSAW.endpointIsLegalSAW](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWColumns.lean)
-/
@[path]
private lemma endpointIsLegalSAW_eq
  {w : HexWalk}
-- given
  (h : w.IsLegalSAW) :
-- imply
  w.EndpointIsLegalSAW := by
-- proof
  apply StatMech.Universality.HexWalk.IsLegalSAW.endpointIsLegalSAW h

/--
[HLHCCanonicalColumnWalk.mem_topAtWidth](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWColumns.lean)
-/
@[path]
private lemma mem_topAtWidth_eq
  {T : ℕ}
  {ts : List ℤ}
  {W : HLHCCanonicalColumnWalk T ts}
-- given
  (hT : 0 < T) :
-- imply
  HexCSTopWalkAtWidth T hT ts := by
-- proof
  apply StatMech.Universality.HLHCCanonicalColumnWalk.mem_topAtWidth W hT

/--
[HLHCMidpointColumnWalk.midCoord_mem_vertexSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWColumns.lean)
-/
@[path]
private lemma midCoord_mem_vertexSet_eq
  {T : ℕ}
  {ts : List ℤ}
  {W : HLHCMidpointColumnWalk T ts}
  {k : Fin ts.length} :
-- imply
  W.midCoord k ∈ hexCSVertexSet T W.stripHeight := by
-- proof
  apply StatMech.Universality.HLHCMidpointColumnWalk.midCoord_mem_vertexSet W k

/--
[HLHCMidpointColumnWalk.top_mem_vertexSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWColumns.lean)
-/
@[path]
private lemma top_mem_vertexSet_eq_2
  {T : ℕ}
  {ts : List ℤ}
  {W : HLHCMidpointColumnWalk T ts}
-- given
  (hT : 0 < T) :
-- imply
  W.topCoord ∈ hexCSVertexSet T W.stripHeight := by
-- proof
  apply StatMech.Universality.HLHCMidpointColumnWalk.top_mem_vertexSet W hT

/--
[HLHCMidpointColumnWalk.mem_topAtWidth](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWColumns.lean)
-/
@[path]
private lemma mem_topAtWidth_eq_2
  {T : ℕ}
  {ts : List ℤ}
  {W : HLHCMidpointColumnWalk T ts}
-- given
  (hT : 0 < T) :
-- imply
  HexCSTopWalkAtWidth T hT ts := by
-- proof
  apply StatMech.Universality.HLHCMidpointColumnWalk.mem_topAtWidth W hT


-- created on 2026-10-23
