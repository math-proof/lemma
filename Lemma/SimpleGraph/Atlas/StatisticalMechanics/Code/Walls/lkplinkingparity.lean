import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.lkplinkingparity
open Finset SimpleGraph StatMech StatMech.Walls


/--
[lkp_bdEdge_iff_windColour](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/lkplinkingparity.lean)
-/
@[path]
private lemma lkp_bdEdge_iff_windColour_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {u v : Site 2}
-- given
  (_hadj : (hypercubicLattice 2).Adj u v) :
-- imply
  bdEdge (jec_leftRegion Vc) s(u, v) ↔ lkp_windColour Vc u ≠ lkp_windColour Vc v := by
-- proof
  apply StatMech.Walls.lkp_bdEdge_iff_windColour Vc _hadj

/--
[lkp_leftRegion_crossCount_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/lkplinkingparity.lean)
-/
@[path]
private lemma lkp_leftRegion_crossCount_even_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {x : Site 2}
  {p : (hypercubicLattice 2).Walk x x} :
-- imply
  Even (crossCount (jec_leftRegion Vc) p) := by
-- proof
  apply StatMech.Walls.lkp_leftRegion_crossCount_even Vc p

/--
[lkp_linkingEven_of_agrees_windBoundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/lkplinkingparity.lean)
-/
@[path]
private lemma lkp_linkingEven_of_agrees_windBoundary_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {δ : Finset (Sym2 (Site 2))}
-- given
  (hδ : ∀ {u v : Site 2}, (hypercubicLattice 2).Adj u v → (s(u, v) ∈ δ ↔ bdEdge (jec_leftRegion Vc) s(u, v))) :
-- imply
  kwf_LinkingEven δ := by
-- proof
  apply StatMech.Walls.lkp_linkingEven_of_agrees_windBoundary Vc hδ

/--
[lkp_edges_agree_windBoundary_of_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/lkplinkingparity.lean)
-/
@[path]
private lemma lkp_edges_agree_windBoundary_of_bridge_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {u v : Site 2}
-- given
  (hbridge : rpc_CrossEdgeOddIffOnWalk Vc)
  (hadj : (hypercubicLattice 2).Adj u v) :
-- imply
  s(u, v) ∈ Vc.edges.toFinset ↔ bdEdge (jec_leftRegion Vc) s(u, v) := by
-- proof
  apply StatMech.Walls.lkp_edges_agree_windBoundary_of_bridge Vc hbridge hadj

/--
[lkp_latLinkingParity_of_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/lkplinkingparity.lean)
-/
@[path]
private lemma lkp_latLinkingParity_of_bridge_eq
-- given
  (hbridge : ∀ {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a), rpc_CrossEdgeOddIffOnWalk Vc) :
-- imply
  kwf_LatLinkingParity := by
-- proof
  apply StatMech.Walls.lkp_latLinkingParity_of_bridge hbridge

/--
[lkp_latLinkingParity_of_windingMatch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/lkplinkingparity.lean)
-/
@[path]
private lemma lkp_latLinkingParity_of_windingMatch_eq
-- given
  (hbridge : ∀ {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a), rpc_CrossEdgeOddIffOnWalk Vc) :
-- imply
  kwf_LatLinkingParity ∧ kwc_PrimalWalkLeftRegionMatch := by
-- proof
  apply StatMech.Walls.lkp_latLinkingParity_of_windingMatch hbridge

/--
[lkp_unitSquare_crossCount_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/lkplinkingparity.lean)
-/
@[path]
private lemma lkp_unitSquare_crossCount_even_eq :
-- imply
  Even (crossCount (jec_leftRegion wwit_unitSquareLoop) wwit_unitSquareLoop) := by
-- proof
  apply StatMech.Walls.lkp_unitSquare_crossCount_even

/--
[lkp_unitSquare_windColour_separates](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/lkplinkingparity.lean)
-/
@[path]
private lemma lkp_unitSquare_windColour_separates_eq :
-- imply
  lkp_windColour wwit_unitSquareLoop (![1, 1] : Site 2) ≠ lkp_windColour wwit_unitSquareLoop (![0, 1] : Site 2) := by
-- proof
  apply StatMech.Walls.lkp_unitSquare_windColour_separates


-- created on 2026-10-23
