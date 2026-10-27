import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.FaceDualDichotomy
open Set SimpleGraph StatMech.Lattice StatMech.RSW.Box StatMech StatMech.Universality


/--
[fdd_faceBoundary_dualEdge_isLatticeEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/FaceDualDichotomy.lean)
-/
@[path]
private lemma fdd_faceBoundary_dualEdge_isLatticeEdge_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {f g : Site 2}
-- given
  (h : (hypercubicLattice 2).Adj f g) :
-- imply
  ∃ p q : Site 2, crossEdge (sharedPrimalEdge f g) = s(rot90Fun p, rot90Fun q) ∧ (hypercubicLattice 2).Adj (rot90Fun p) (rot90Fun q) := by
-- proof
  apply StatMech.Universality.fdd_faceBoundary_dualEdge_isLatticeEdge h

/--
[fdd_faceBoundary_edge_dual_open](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/FaceDualDichotomy.lean)
-/
@[path]
private lemma fdd_faceBoundary_edge_dual_open_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {ω : ConfigSpace (Sym2 (Site 2))}
  {f g : Site 2}
-- given
  (hclosed : ω (sharedPrimalEdge f g) = false) :
-- imply
  dualConfig ω (crossEdge (sharedPrimalEdge f g)) = true := by
-- proof
  apply StatMech.Universality.fdd_faceBoundary_edge_dual_open ω hclosed

/--
[fdd_faceBoundaryGraph_dualAdj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/FaceDualDichotomy.lean)
-/
@[path]
private lemma fdd_faceBoundaryGraph_dualAdj_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {ω : ConfigSpace (Sym2 (Site 2))}
  {p q : Site 2}
-- given
  (hadj : (hypercubicLattice 2).Adj p q)
  (hclosed : ω s(p, q) = false) :
-- imply
  (openSubgraph 2 (dualConfig ω)).Adj (rot90Fun p) (rot90Fun q) := by
-- proof
  apply StatMech.Universality.fdd_faceBoundaryGraph_dualAdj ω hadj hclosed

/--
[fdd_cluster_faceBoundary_edge_dual_open](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/FaceDualDichotomy.lean)
-/
@[path]
private lemma fdd_cluster_faceBoundary_edge_dual_open_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {o : Site 2}
  {f g : Site 2}
-- given
  (h : (faceBoundaryGraph (cluster 2 ω o)).Adj f g) :
-- imply
  dualConfig ω (crossEdge (sharedPrimalEdge f g)) = true := by
-- proof
  apply StatMech.Universality.fdd_cluster_faceBoundary_edge_dual_open o h

/--
[fdd_cluster_dualCircuit_open](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/FaceDualDichotomy.lean)
-/
@[path]
private lemma fdd_cluster_dualCircuit_open_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {o : Site 2}
  {z : Site 2}
  {w : (hypercubicLattice 2).Walk o z}
-- given
  (hfin : (cluster 2 ω o).Finite)
  (hz : z ∉ cluster 2 ω o) :
-- imply
  ∃ (u : Site 2) (c : (faceBoundaryGraph (cluster 2 ω o)).Walk u u), c.IsCycle ∧ (∀ {f g : Site 2}, s(f, g) ∈ c.edges → dualConfig ω (crossEdge (sharedPrimalEdge f g)) = true) := by
-- proof
  apply StatMech.Universality.fdd_cluster_dualCircuit_open o hfin w hz

/--
[fdd_leftReach_barrierEdge_dualAdj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/FaceDualDichotomy.lean)
-/
@[path]
private lemma fdd_leftReach_barrierEdge_dualAdj_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {v w : Site 2}
-- given
  (hv : v ∈ bcd_leftReach ω n)
  (hwbox : w ∈ rect 0 n 0 n)
  (hadj : (hypercubicLattice 2).Adj v w)
  (hw : w ∉ bcd_leftReach ω n) :
-- imply
  (openSubgraph 2 (dualConfig ω)).Adj (rot90Fun v) (rot90Fun w) := by
-- proof
  apply StatMech.Universality.fdd_leftReach_barrierEdge_dualAdj ω n hv hwbox hadj hw

/--
[fdd_leftReach_faceBoundary_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/FaceDualDichotomy.lean)
-/
@[path]
private lemma fdd_leftReach_faceBoundary_adj_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {v w : Site 2}
-- given
  (hv : v ∈ bcd_leftReach ω n)
  (hw : w ∉ bcd_leftReach ω n)
  (hadj : (hypercubicLattice 2).Adj v w) :
-- imply
  ∃ f g : Site 2, (faceBoundaryGraph (bcd_leftReach ω n)).Adj f g := by
-- proof
  apply StatMech.Universality.fdd_leftReach_faceBoundary_adj ω n hv hw hadj

/--
[fdd_leftReach_faceBoundary_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/FaceDualDichotomy.lean)
-/
@[path]
private lemma fdd_leftReach_faceBoundary_nonempty_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
-- given
  (hn : 0 ≤ n)
  (hnoH : ¬ HorizontalCrossing ω 0 n 0 n) :
-- imply
  ∃ f g : Site 2, (faceBoundaryGraph (bcd_leftReach ω n)).Adj f g := by
-- proof
  apply StatMech.Universality.fdd_leftReach_faceBoundary_nonempty ω n hn hnoH

/--
[fdd_leftReach_dualCircuit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/FaceDualDichotomy.lean)
-/
@[path]
private lemma fdd_leftReach_dualCircuit_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
-- given
  (hn : 0 ≤ n)
  (hnoH : ¬ HorizontalCrossing ω 0 n 0 n) :
-- imply
  ∃ (u : Site 2) (c : (faceBoundaryGraph (bcd_leftReach ω n)).Walk u u), c.IsCycle := by
-- proof
  apply StatMech.Universality.fdd_leftReach_dualCircuit ω n hn hnoH

/--
[fdd_dualEdge_leftSide](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/FaceDualDichotomy.lean)
-/
@[path]
private lemma fdd_dualEdge_leftSide_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {a b : ℤ} :
-- imply
  crossEdge (sharedPrimalEdge ![a, b] ![a - 1, b]) = s(![-b, a], ![-(b + 1), a]) := by
-- proof
  apply StatMech.Universality.fdd_dualEdge_leftSide a b

/--
[fdd_dualEdge_rightSide](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/FaceDualDichotomy.lean)
-/
@[path]
private lemma fdd_dualEdge_rightSide_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {a b : ℤ} :
-- imply
  crossEdge (sharedPrimalEdge ![a, b] ![a + 1, b]) = s(![-b, a + 1], ![-(b + 1), a + 1]) := by
-- proof
  apply StatMech.Universality.fdd_dualEdge_rightSide a b

/--
[fdd_straight_dualEdges_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/FaceDualDichotomy.lean)
-/
@[path]
private lemma fdd_straight_dualEdges_disjoint_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {a b : ℤ}
  {p : Site 2}
-- given
  (hp1 : p ∈ crossEdge (sharedPrimalEdge ![a, b] ![a - 1, b]))
  (hp2 : p ∈ crossEdge (sharedPrimalEdge ![a, b] ![a + 1, b])) :
-- imply
  False := by
-- proof
  apply StatMech.Universality.fdd_straight_dualEdges_disjoint a b hp1 hp2

/--
[fdd_square_dichotomy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/FaceDualDichotomy.lean)
-/
@[path]
private lemma fdd_square_dichotomy_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
-- given
  (hn : 0 ≤ n)
  (hnoH : ¬ HorizontalCrossing ω 0 n 0 n) :
-- imply
  (bcd_leftReach ω n).Finite ∧ (∀ {v w : Site 2}, v ∈ bcd_leftReach ω n → w ∈ rect 0 n 0 n → (hypercubicLattice 2).Adj v w → w ∉ bcd_leftReach ω n → (openSubgraph 2 (dualConfig ω)).Adj (rot90Fun v) (rot90Fun w)) ∧ (∃ f g : Site 2, (faceBoundaryGraph (bcd_leftReach ω n)).Adj f g) ∧ (∃ (u : Site 2) (c : (faceBoundaryGraph (bcd_leftReach ω n)).Walk u u), c.IsCycle) := by
-- proof
  apply StatMech.Universality.fdd_square_dichotomy ω n hn hnoH


-- created on 2026-10-23
