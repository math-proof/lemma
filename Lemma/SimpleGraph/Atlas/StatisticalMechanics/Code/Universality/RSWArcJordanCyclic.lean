import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.RSWArcJordanCyclic
open Function MeasureTheory Set StatMech StatMech.Universality


/--
[rlc_orderedContourArc_edges_disjoint_complementary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWArcJordanCyclic.lean)
-/
@[path]
private lemma rlc_orderedContourArc_edges_disjoint_complementary_eq
  {H : SimpleGraph (Site 2)}
  {u x y : Site 2}
  {c : H.Walk u u}
-- given
  (hc : c.IsTrail)
  (hx : x ∈ c.support)
  (hy : y ∈ c.support) :
-- imply
  (rlc_orderedContourArc c hx hy).edges.Disjoint (rlc_complementaryContourArc c hx hy).edges := by
-- proof
  apply StatMech.Universality.rlc_orderedContourArc_edges_disjoint_complementary c hc hx hy

/--
[rlc_not_contourArcLocalSide_iff_bad_edges_both](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWArcJordanCyclic.lean)
-/
@[path]
private lemma rlc_not_contourArcLocalSide_iff_bad_edges_both_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {omega : ConfigSpace (Sym2 (Site 2))}
  {u x y : Site 2}
  {c : (faceBoundaryGraph (rlc_mixedWiredReachSet G omega)).Walk u u}
-- given
  (hc : c.IsTrail)
  (hx : x ∈ c.support)
  (hy : y ∈ c.support) :
-- imply
  ¬ RlcContourArcLocalSide G omega c hx hy ↔ ∃ f₁ g₁ f₂ g₂ : Site 2, s(f₁, g₁) ∈ (rlc_orderedContourArc c hx hy).edges ∧ ¬ rlc_contourEdgeLocal G f₁ g₁ ∧ s(f₂, g₂) ∈ (rlc_complementaryContourArc c hx hy).edges ∧ ¬ rlc_contourEdgeLocal G f₂ g₂ ∧ s(f₁, g₁) ≠ s(f₂, g₂) := by
-- proof
  apply StatMech.Universality.rlc_not_contourArcLocalSide_iff_bad_edges_both G omega c hc hx hy

/--
[rlc_contourArcLocalSide_of_atMostOne_bad_edge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWArcJordanCyclic.lean)
-/
@[path]
private lemma rlc_contourArcLocalSide_of_atMostOne_bad_edge_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {omega : ConfigSpace (Sym2 (Site 2))}
  {u x y : Site 2}
  {c : (faceBoundaryGraph (rlc_mixedWiredReachSet G omega)).Walk u u}
-- given
  (hc : c.IsTrail)
  (hx : x ∈ c.support)
  (hy : y ∈ c.support)
  (hbad : ∀ {f₁ g₁ f₂ g₂ : Site 2}, s(f₁, g₁) ∈ c.edges → ¬ rlc_contourEdgeLocal G f₁ g₁ → s(f₂, g₂) ∈ c.edges → ¬ rlc_contourEdgeLocal G f₂ g₂ → s(f₁, g₁) = s(f₂, g₂)) :
-- imply
  RlcContourArcLocalSide G omega c hx hy := by
-- proof
  apply StatMech.Universality.rlc_contourArcLocalSide_of_atMostOne_bad_edge G omega c hc hx hy hbad

/--
[rlc_mixedWired_exists_faceBoundary_not_local](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWArcJordanCyclic.lean)
-/
@[path]
private lemma rlc_mixedWired_exists_faceBoundary_not_local_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {omega : ConfigSpace (Sym2 (Site 2))}
-- given
  (hn : 0 < n)
  (hlt : G.lower + 1 < G.upper) :
-- imply
  ∃ f g : Site 2, (faceBoundaryGraph (rlc_mixedWiredReachSet G omega)).Adj f g ∧ ¬ rlc_reflectedTargetLocallySupported G s(rlc_dualReflect f, rlc_dualReflect g) ∧ ¬ rlc_boundarySourceLocallySupported G (sharedPrimalEdge f g) := by
-- proof
  apply StatMech.Universality.rlc_mixedWired_exists_faceBoundary_not_local G hn hlt omega


-- created on 2026-10-23
