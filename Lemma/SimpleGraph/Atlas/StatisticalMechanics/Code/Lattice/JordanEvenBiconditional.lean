import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Lattice.JordanEvenBiconditional.Part5
open SimpleGraph Set StatMech StatMech.Lattice


/--
[jeb_degree_induce_eq_of_neighborSet_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEvenBiconditional.lean)
-/
@[path]
private lemma jeb_degree_induce_eq_of_neighborSet_subset_eq
  {H : SimpleGraph V}
  [SimpleGraph.LocallyFinite H]
  {s : Set V}
  {v : s}
-- given
  (hsub : H.neighborSet ↑v ⊆ s) :
-- imply
  @SimpleGraph.degree _ (H.induce s) v (jeb_induceLF H s v) = H.degree ↑v := by
-- proof
  apply StatMech.Lattice.jeb_degree_induce_eq_of_neighborSet_subset H s v hsub

/--
[jeb_degree_induce_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEvenBiconditional.lean)
-/
@[path]
private lemma jeb_degree_induce_eq_eq
  {H : SimpleGraph V}
  [SimpleGraph.LocallyFinite H]
  {s : Set V}
  {v : s}
-- given
  (hsupp : H.support ⊆ s) :
-- imply
  @SimpleGraph.degree _ (H.induce s) v (jeb_induceLF H s v) = H.degree ↑v := by
-- proof
  apply StatMech.Lattice.jeb_degree_induce_eq H s hsupp v

/--
[jeb_degree_induce_eq'](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEvenBiconditional.lean)
-/
@[path]
private lemma jeb_degree_induce_eq'_eq
  {H : SimpleGraph V}
  [SimpleGraph.LocallyFinite H]
  {s : Set V}
  {v : s}
  [inst : Fintype ((H.induce s).neighborSet v)]
-- given
  (hsub : H.neighborSet ↑v ⊆ s) :
-- imply
  (H.induce s).degree v = H.degree ↑v := by
-- proof
  apply StatMech.Lattice.jeb_degree_induce_eq' H s v hsub

/--
[jeb_neighborSet_subset_component](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEvenBiconditional.lean)
-/
@[path]
private lemma jeb_neighborSet_subset_component_eq
  {G : SimpleGraph V}
  {C : G.ConnectedComponent}
  {v : (C.supp : Set V)} :
-- imply
  G.neighborSet ↑v ⊆ (C.supp : Set V) := by
-- proof
  apply StatMech.Lattice.jeb_neighborSet_subset_component G C v

/--
[jeb_two_odd_reachable_fin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEvenBiconditional.lean)
-/
@[path]
private lemma jeb_two_odd_reachable_fin_eq
  [Fintype V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : V}
-- given
  (hp : Odd (G.degree p))
  (hq : Odd (G.degree q))
  (hother : ∀ v, v ≠ p → v ≠ q → Even (G.degree v)) :
-- imply
  G.Reachable p q := by
-- proof
  apply StatMech.Lattice.jeb_two_odd_reachable_fin G p q hp hq hother

/--
[jeb_support_finite_of_edgeSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEvenBiconditional.lean)
-/
@[path]
private lemma jeb_support_finite_of_edgeSet_eq
  {H : SimpleGraph V}
  [Fintype H.edgeSet] :
-- imply
  H.support.Finite := by
-- proof
  apply StatMech.Lattice.jeb_support_finite_of_edgeSet H

/--
[jeb_two_odd_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEvenBiconditional.lean)
-/
@[path]
private lemma jeb_two_odd_reachable_eq
  {H : SimpleGraph V}
  [SimpleGraph.LocallyFinite H]
  {p q : V}
-- given
  (hfin : H.support.Finite)
  (hp : Odd (H.degree p))
  (hq : Odd (H.degree q))
  (hother : ∀ v, v ≠ p → v ≠ q → Even (H.degree v)) :
-- imply
  H.Reachable p q := by
-- proof
  apply StatMech.Lattice.jeb_two_odd_reachable H hfin p q hp hq hother

/--
[jeb_two_odd_reachable_of_edgeSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEvenBiconditional.lean)
-/
@[path]
private lemma jeb_two_odd_reachable_of_edgeSet_eq
  {H : SimpleGraph V}
  [SimpleGraph.LocallyFinite H]
  [Fintype H.edgeSet]
  {p q : V}
-- given
  (hp : Odd (H.degree p))
  (hq : Odd (H.degree q))
  (hother : ∀ v, v ≠ p → v ≠ q → Even (H.degree v)) :
-- imply
  H.Reachable p q := by
-- proof
  apply StatMech.Lattice.jeb_two_odd_reachable_of_edgeSet H p q hp hq hother

/--
[jeb_site_eq_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEvenBiconditional.lean)
-/
@[path]
private lemma jeb_site_eq_iff_eq
  {x : Site 2}
  {c d : ℤ} :
-- imply
  x = ![c, d] ↔ x 0 = c ∧ x 1 = d := by
-- proof
  apply StatMech.Lattice.jeb_site_eq_iff x c d

/--
[jeb_jce_nbr_inj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEvenBiconditional.lean)
-/
@[path]
private lemma jeb_jce_nbr_inj_eq
  {v : Site 2} :
-- imply
  Function.Injective (jce_nbr v) := by
-- proof
  apply StatMech.Lattice.jeb_jce_nbr_inj v

/--
[jeb_exists_jce_nbr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEvenBiconditional.lean)
-/
@[path]
private lemma jeb_exists_jce_nbr_eq
  {v w : Site 2}
-- given
  (h : (hypercubicLattice 2).Adj v w) :
-- imply
  ∃ i : Fin 4, w = jce_nbr v i := by
-- proof
  apply StatMech.Lattice.jeb_exists_jce_nbr v w h

/--
[jeb_jce_degree_eq_degree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEvenBiconditional.lean)
-/
@[path]
private lemma jeb_jce_degree_eq_degree_eq
  {H : SimpleGraph (Site 2)}
  [SimpleGraph.LocallyFinite H]
  {v : Site 2}
-- given
  (hsub : H ≤ hypercubicLattice 2) :
-- imply
  jce_degree H.edgeSet v = H.degree v := by
-- proof
  apply StatMech.Lattice.jeb_jce_degree_eq_degree H hsub v

/--
[jeb_jce_degree_insert_endpoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEvenBiconditional.lean)
-/
@[path]
private lemma jeb_jce_degree_insert_endpoint_eq
  {E : Set (Sym2 (Site 2))}
  {p q : Site 2}
-- given
  (hpq : (hypercubicLattice 2).Adj p q)
  (hnpq : s(p, q) ∉ E) :
-- imply
  jce_degree (insert (s(p,q)) E) p = jce_degree E p + 1 := by
-- proof
  apply StatMech.Lattice.jeb_jce_degree_insert_endpoint E p q hpq hnpq

/--
[jeb_jce_degree_insert_other](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEvenBiconditional.lean)
-/
@[path]
private lemma jeb_jce_degree_insert_other_eq
  {E : Set (Sym2 (Site 2))}
  {p q v : Site 2}
-- given
  (hvp : v ≠ p)
  (hvq : v ≠ q) :
-- imply
  jce_degree (insert (s(p,q)) E) v = jce_degree E v := by
-- proof
  apply StatMech.Lattice.jeb_jce_degree_insert_other E p q v hvp hvq

/--
[jeb_degree_data_of_closedContour](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEvenBiconditional.lean)
-/
@[path]
private lemma jeb_degree_data_of_closedContour_eq
  {H : SimpleGraph (Site 2)}
  [SimpleGraph.LocallyFinite H]
  {p q : Site 2}
-- given
  (hsub : H ≤ hypercubicLattice 2)
  (hpq : (hypercubicLattice 2).Adj p q)
  (hnpq : s(p, q) ∉ H.edgeSet)
  (hcc : jce_ClosedContour (insert (s(p,q)) H.edgeSet)) :
-- imply
  Odd (H.degree p) ∧ Odd (H.degree q) ∧ (∀ v, v ≠ p → v ≠ q → Even (H.degree v)) := by
-- proof
  apply StatMech.Lattice.jeb_degree_data_of_closedContour H hsub p q hpq hnpq hcc

/--
[jeb_reachable_of_closedContour](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEvenBiconditional.lean)
-/
@[path]
private lemma jeb_reachable_of_closedContour_eq
  {H : SimpleGraph (Site 2)}
  [SimpleGraph.LocallyFinite H]
  [Fintype H.edgeSet]
  {p q : Site 2}
-- given
  (hsub : H ≤ hypercubicLattice 2)
  (hpq : (hypercubicLattice 2).Adj p q)
  (hnpq : s(p, q) ∉ H.edgeSet)
  (hcc : jce_ClosedContour (insert (s(p,q)) H.edgeSet)) :
-- imply
  H.Reachable p q := by
-- proof
  apply StatMech.Lattice.jeb_reachable_of_closedContour H hsub p q hpq hnpq hcc

/--
[jeb_contourSet_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEvenBiconditional.lean)
-/
@[path]
private lemma jeb_contourSet_eq_eq
  {H : SimpleGraph (Site 2)}
  [Fintype H.edgeSet]
  {p q f0 g0 : Site 2}
-- given
  (hshared : sharedPrimalEdge f0 g0 = s(p, q)) :
-- imply
  ((insert (sharedPrimalEdge f0 g0) H.edgeSet.toFinset : Finset (Sym2 (Site 2))) : Set (Sym2 (Site 2))) = insert (s(p, q)) H.edgeSet := by
-- proof
  apply StatMech.Lattice.jeb_contourSet_eq H p q f0 g0 hshared

/--
[jeb_correctWhitney_of_evenDegree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEvenBiconditional.lean)
-/
@[path]
private lemma jeb_correctWhitney_of_evenDegree_eq
  {H : SimpleGraph (Site 2)}
  [SimpleGraph.LocallyFinite H]
  [Fintype H.edgeSet]
  {p q f0 g0 : Site 2}
-- given
  (hsub : H ≤ hypercubicLattice 2)
  (hpq : (hypercubicLattice 2).Adj p q)
  (hnpq : s(p, q) ∉ H.edgeSet)
  (hfg : (hypercubicLattice 2).Adj f0 g0)
  (hshared : sharedPrimalEdge f0 g0 = s(p, q))
  (hcc : jce_ClosedContour ((insert (sharedPrimalEdge f0 g0) H.edgeSet.toFinset : Finset (Sym2 (Site 2))) : Set (Sym2 (Site 2)))) :
-- imply
  (H.Reachable p q ↔ ¬ ((whb_faceRegion H).deleteEdges {s(f0, g0)}).Reachable f0 g0) := by
-- proof
  apply StatMech.Lattice.jeb_correctWhitney_of_evenDegree H hsub p q f0 g0 hpq hnpq hfg hshared hcc

/--
[jeb_imageGraph_support_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEvenBiconditional.lean)
-/
@[path]
private lemma jeb_imageGraph_support_finite_eq
  {P : PlanarZ2Subgraph} :
-- imply
  (imageGraph P).support.Finite := by
-- proof
  apply StatMech.Lattice.jeb_imageGraph_support_finite P

/--
[jeb_correctWhitney_imageGraph](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEvenBiconditional.lean)
-/
@[path]
private lemma jeb_correctWhitney_imageGraph_eq
  {P : PlanarZ2Subgraph}
  {p q f0 g0 : Site 2}
-- given
  (hpq : (hypercubicLattice 2).Adj p q)
  (hnpq : s(p, q) ∉ (imageGraph P).edgeSet)
  (hfg : (hypercubicLattice 2).Adj f0 g0)
  (hshared : sharedPrimalEdge f0 g0 = s(p, q))
  (hcc : jce_ClosedContour ((insert (sharedPrimalEdge f0 g0) (imageGraph P).edgeSet.toFinset : Finset (Sym2 (Site 2))) : Set (Sym2 (Site 2)))) :
-- imply
  ((imageGraph P).Reachable p q ↔ ¬ ((whb_faceRegion (imageGraph P)).deleteEdges {s(f0, g0)}).Reachable f0 g0) := by
-- proof
  apply StatMech.Lattice.jeb_correctWhitney_imageGraph P p q f0 g0 hpq hnpq hfg hshared hcc

/--
[jeb_faithfulDiscreteJordan_of_residue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEvenBiconditional.lean)
-/
@[path]
private lemma jeb_faithfulDiscreteJordan_of_residue_eq
  {P : PlanarZ2Subgraph}
-- given
  (hres : jeb_FaithfulCountResidue)
  (hP : jeb_EvenDegreeSubgraph P) :
-- imply
  whc_FaithfulDiscreteJordan P := by
-- proof
  apply StatMech.Lattice.jeb_faithfulDiscreteJordan_of_residue hres P hP

/--
[jeb_unitSquare_interior_bounded](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEvenBiconditional.lean)
-/
@[path]
private lemma jeb_unitSquare_interior_bounded_eq :
-- imply
  Nonempty {c : (whb_faceRegion (imageGraph jbc_Pce)).ConnectedComponent // c.supp.Finite} := by
-- proof
  apply StatMech.Lattice.jeb_unitSquare_interior_bounded

/--
[jeb_Htest_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEvenBiconditional.lean)
-/
@[path]
private lemma jeb_Htest_le_eq :
-- imply
  whc_Htest ≤ hypercubicLattice 2 := by
-- proof
  apply StatMech.Lattice.jeb_Htest_le

/--
[jeb_square_closedContour](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEvenBiconditional.lean)
-/
@[path]
private lemma jeb_square_closedContour_eq :
-- imply
  jce_ClosedContour (imageGraph jbc_Pce).edgeSet := by
-- proof
  apply StatMech.Lattice.jeb_square_closedContour

/--
[jeb_Htest_insert_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEvenBiconditional.lean)
-/
@[path]
private lemma jeb_Htest_insert_eq_eq :
-- imply
  insert (s(![(0:ℤ), 0], ![1, 0])) whc_Htest.edgeSet = (imageGraph jbc_Pce).edgeSet := by
-- proof
  apply StatMech.Lattice.jeb_Htest_insert_eq

/--
[jeb_unitSquare_biconditional_fires](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEvenBiconditional.lean)
-/
@[path]
private lemma jeb_unitSquare_biconditional_fires_eq :
-- imply
  (whc_Htest.Reachable ![(0:ℤ), 0] ![(1:ℤ), 0] ↔ ¬ ((whb_faceRegion whc_Htest).deleteEdges {s(![(0:ℤ), 0], ![(0:ℤ), -1])}).Reachable ![(0:ℤ), 0] ![(0:ℤ), -1]) := by
-- proof
  apply StatMech.Lattice.jeb_unitSquare_biconditional_fires


-- created on 2026-10-23
