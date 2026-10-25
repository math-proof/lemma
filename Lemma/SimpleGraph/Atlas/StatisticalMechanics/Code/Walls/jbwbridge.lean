import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.jbwbridge.Part3
open SimpleGraph Set StatMech StatMech.Walls


/--
[jbw_mem_bdEdgeSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jbwbridge.lean)
-/
@[path]
private lemma jbw_mem_bdEdgeSet_eq
  {S : Set (Site 2)}
  {e : Sym2 (Site 2)} :
-- imply
  e ∈ jbw_bdEdgeSet S ↔ bdEdge S e := by
-- proof
  apply StatMech.Walls.jbw_mem_bdEdgeSet S e

/--
[jbw_vertexCut_not_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jbwbridge.lean)
-/
@[path]
private lemma jbw_vertexCut_not_even_eq :
-- imply
  ¬ Even (jce_degree (jbw_bdEdgeSet jbw_singleton) ![(1 : ℤ), 0]) := by
-- proof
  apply StatMech.Walls.jbw_vertexCut_not_even

/--
[jbw_jed_reachability](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jbwbridge.lean)
-/
@[path]
private lemma jbw_jed_reachability_eq
  {H : SimpleGraph (Site 2)}
  {p q f0 g0 : Site 2}
-- given
  (hfin : H.edgeSet.Finite)
  (hpq : (hypercubicLattice 2).Adj p q)
  (hnpq : s(p, q) ∉ H.edgeSet)
  (hfg : (hypercubicLattice 2).Adj f0 g0)
  (hshared : sharedPrimalEdge f0 g0 = s(p, q))
  (hsep : ¬ ((whb_faceRegion H).deleteEdges {s(f0, g0)}).Reachable f0 g0) :
-- imply
  H.Reachable p q := by
-- proof
  apply StatMech.Walls.jbw_jed_reachability H hfin p q f0 g0 hpq hnpq hfg hshared hsep

/--
[jbw_easyHalf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jbwbridge.lean)
-/
@[path]
private lemma jbw_easyHalf_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {u v : Site 2}
-- given
  (hadj : (hypercubicLattice 2).Adj u v)
  (hbd : bdEdge (jec_leftRegion Vc) s(u, v)) :
-- imply
  u ∈ Vc.support ∨ v ∈ Vc.support := by
-- proof
  apply StatMech.Walls.jbw_easyHalf Vc hadj hbd

/--
[jbw_hardGap_iff_windingBody](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jbwbridge.lean)
-/
@[path]
private lemma jbw_hardGap_iff_windingBody_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a} :
-- imply
  (jbw_hard_gap Vc ∧ ∀ {u v : Site 2}, (hypercubicLattice 2).Adj u v → bdEdge (jec_leftRegion Vc) s(u, v) → s(u, v) ∈ Vc.edges.toFinset) ↔ (∀ {u v : Site 2}, (hypercubicLattice 2).Adj u v → (s(u, v) ∈ Vc.edges.toFinset ↔ bdEdge (jec_leftRegion Vc) s(u, v))) := by
-- proof
  apply StatMech.Walls.jbw_hardGap_iff_windingBody Vc

/--
[jbw_hard_gap_of_windingMatch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jbwbridge.lean)
-/
@[path]
private lemma jbw_hard_gap_of_windingMatch_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
-- given
  (hmatch : kwc_PrimalWalkLeftRegionMatch) :
-- imply
  jbw_hard_gap Vc := by
-- proof
  apply StatMech.Walls.jbw_hard_gap_of_windingMatch hmatch Vc

/--
[jbw_jed_insufficient](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jbwbridge.lean)
-/
@[path]
private lemma jbw_jed_insufficient_eq :
-- imply
  (¬ Even (jce_degree (jbw_bdEdgeSet jbw_singleton) ![(1 : ℤ), 0])) ∧ (∀ (H : SimpleGraph (Site 2)), H.edgeSet.Finite → ∀ (p q f0 g0 : Site 2), (hypercubicLattice 2).Adj p q → s(p, q) ∉ H.edgeSet → (hypercubicLattice 2).Adj f0 g0 → sharedPrimalEdge f0 g0 = s(p, q) → ¬ ((whb_faceRegion H).deleteEdges {s(f0, g0)}).Reachable f0 g0 → H.Reachable p q) ∧ (kwc_PrimalWalkLeftRegionMatch → ∀ {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a), jbw_hard_gap Vc) := by
-- proof
  apply StatMech.Walls.jbw_jed_insufficient


-- created on 2026-10-23
