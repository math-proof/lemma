import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.FrameChangeIso.Part8
open Set SimpleGraph MeasureTheory ProbabilityTheory StatMech.Lattice StatMech.RSW.Box StatMech StatMech.Universality


/--
[fci_faceBoundaryGraph_le_dualLattice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/FrameChangeIso.lean)
-/
@[path]
private lemma fci_faceBoundaryGraph_le_dualLattice_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {S : Set (Site 2)} :
-- imply
  faceBoundaryGraph S ≤ dualLattice := by
-- proof
  apply StatMech.Universality.fci_faceBoundaryGraph_le_dualLattice S

/--
[fci_faceWalk_to_dualWalk_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/FrameChangeIso.lean)
-/
@[path]
private lemma fci_faceWalk_to_dualWalk_support_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {S : Set (Site 2)}
  {u v : Site 2}
  {c : (faceBoundaryGraph S).Walk u v} :
-- imply
  (fci_faceWalk_to_dualWalk S c).support = c.support := by
-- proof
  apply StatMech.Universality.fci_faceWalk_to_dualWalk_support S c

/--
[fci_faceCycle_to_dualCycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/FrameChangeIso.lean)
-/
@[path]
private lemma fci_faceCycle_to_dualCycle_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {S : Set (Site 2)}
  {u : Site 2}
  {c : (faceBoundaryGraph S).Walk u u}
-- given
  (hc : c.IsCycle) :
-- imply
  (fci_faceWalk_to_dualWalk S c).IsCycle := by
-- proof
  apply StatMech.Universality.fci_faceCycle_to_dualCycle S c hc

/--
[fci_faceOpenDual_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/FrameChangeIso.lean)
-/
@[path]
private lemma fci_faceOpenDual_adj_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {ω : ConfigSpace (Sym2 (Site 2))}
  {f g : Site 2} :
-- imply
  (fci_faceOpenDual ω).Adj f g ↔ (hypercubicLattice 2).Adj f g ∧ ω (sharedPrimalEdge f g) = false := by
-- proof
  apply StatMech.Universality.fci_faceOpenDual_adj ω f g

/--
[fci_faceOpenDual_le_dualLattice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/FrameChangeIso.lean)
-/
@[path]
private lemma fci_faceOpenDual_le_dualLattice_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {ω : ConfigSpace (Sym2 (Site 2))} :
-- imply
  fci_faceOpenDual ω ≤ dualLattice := by
-- proof
  apply StatMech.Universality.fci_faceOpenDual_le_dualLattice ω

/--
[fci_faceBoundaryGraph_cluster_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/FrameChangeIso.lean)
-/
@[path]
private lemma fci_faceBoundaryGraph_cluster_le_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {o : Site 2} :
-- imply
  faceBoundaryGraph (cluster 2 ω o) ≤ fci_faceOpenDual ω := by
-- proof
  apply StatMech.Universality.fci_faceBoundaryGraph_cluster_le o

/--
[fci_cluster_faceOpenDual_circuit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/FrameChangeIso.lean)
-/
@[path]
private lemma fci_cluster_faceOpenDual_circuit_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {o : Site 2}
  {z : Site 2}
  {w : (hypercubicLattice 2).Walk o z}
-- given
  (hfin : (cluster 2 ω o).Finite)
  (hz : z ∉ cluster 2 ω o) :
-- imply
  ∃ (u : Site 2) (c : (fci_faceOpenDual ω).Walk u u), c.IsCycle := by
-- proof
  apply StatMech.Universality.fci_cluster_faceOpenDual_circuit o hfin w hz

/--
[fci_leftReach_faceOpenDual_adj_of_closed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/FrameChangeIso.lean)
-/
@[path]
private lemma fci_leftReach_faceOpenDual_adj_of_closed_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {f g : Site 2}
-- given
  (h : (faceBoundaryGraph (bcd_leftReach ω n)).Adj f g)
  (hcl : ω (sharedPrimalEdge f g) = false) :
-- imply
  (fci_faceOpenDual ω).Adj f g := by
-- proof
  apply StatMech.Universality.fci_leftReach_faceOpenDual_adj_of_closed ω n h hcl

/--
[fci_leftReach_faceOpenDual_cycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/FrameChangeIso.lean)
-/
@[path]
private lemma fci_leftReach_faceOpenDual_cycle_eq
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
  apply StatMech.Universality.fci_leftReach_faceOpenDual_cycle ω n hn hnoH

/--
[fci_face_adj_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/FrameChangeIso.lean)
-/
@[path]
private lemma fci_face_adj_left_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {a b : ℤ} :
-- imply
  (hypercubicLattice 2).Adj ![a, b] ![a - 1, b] := by
-- proof
  apply StatMech.Universality.fci_face_adj_left a b

/--
[fci_face_adj_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/FrameChangeIso.lean)
-/
@[path]
private lemma fci_face_adj_right_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {a b : ℤ} :
-- imply
  (hypercubicLattice 2).Adj ![a, b] ![a + 1, b] := by
-- proof
  apply StatMech.Universality.fci_face_adj_right a b

/--
[fci_no_frameChangeIso](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/FrameChangeIso.lean)
-/
@[path]
private lemma fci_no_frameChangeIso_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ} :
-- imply
  ¬ ∃ Φ : Site 2 → Site 2, fci_FrameCompat Φ := by
-- proof
  apply StatMech.Universality.fci_no_frameChangeIso

/--
[fci_no_open_dual_relabel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/FrameChangeIso.lean)
-/
@[path]
private lemma fci_no_open_dual_relabel_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ} :
-- imply
  ¬ ∃ Φ : Site 2 → Site 2, ∀ (f g : Site 2), (hypercubicLattice 2).Adj f g → sharedPrimalEdge f g = s(rot90Inv (Φ f), rot90Inv (Φ g)) := by
-- proof
  apply StatMech.Universality.fci_no_open_dual_relabel

/--
[fci_sharedEdgeRaw_mk_of_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/FrameChangeIso.lean)
-/
@[path]
private lemma fci_sharedEdgeRaw_mk_of_adj_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {f g : Site 2}
-- given
  (h : (hypercubicLattice 2).Adj f g) :
-- imply
  fci_sharedEdgeRaw s(f, g) = sharedPrimalEdge f g := by
-- proof
  apply StatMech.Universality.fci_sharedEdgeRaw_mk_of_adj h

/--
[fci_sharedEdgeMap_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/FrameChangeIso.lean)
-/
@[path]
private lemma fci_sharedEdgeMap_injective_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ} :
-- imply
  Function.Injective fci_sharedEdgeMap := by
-- proof
  apply StatMech.Universality.fci_sharedEdgeMap_injective

/--
[fci_sharedEdgeMap_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/FrameChangeIso.lean)
-/
@[path]
private lemma fci_sharedEdgeMap_surjective_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ} :
-- imply
  Function.Surjective fci_sharedEdgeMap := by
-- proof
  apply StatMech.Universality.fci_sharedEdgeMap_surjective

/--
[fci_faceEdgeEquiv_mk_of_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/FrameChangeIso.lean)
-/
@[path]
private lemma fci_faceEdgeEquiv_mk_of_adj_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {f g : Site 2}
-- given
  (h : (hypercubicLattice 2).Adj f g) :
-- imply
  fci_faceEdgeEquiv s(f, g) = sharedPrimalEdge f g := by
-- proof
  apply StatMech.Universality.fci_faceEdgeEquiv_mk_of_adj h

/--
[fci_faceOpenDual_eq_openSubgraph](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/FrameChangeIso.lean)
-/
@[path]
private lemma fci_faceOpenDual_eq_openSubgraph_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {w : ConfigSpace (Sym2 (Site 2))} :
-- imply
  fci_faceOpenDual w = openSubgraph 2 (fci_faceDualConfig w) := by
-- proof
  apply StatMech.Universality.fci_faceOpenDual_eq_openSubgraph w

/--
[fci_faceDualConfig_measurePreserving](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/FrameChangeIso.lean)
-/
@[path]
private lemma fci_faceDualConfig_measurePreserving_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ} :
-- imply
  MeasurePreserving (fci_faceDualConfig : ConfigSpace (Sym2 (Site 2)) → ConfigSpace (Sym2 (Site 2))) (bernoulliProductMeasure (2⁻¹ : ℝ≥0) half_le_one) (bernoulliProductMeasure (2⁻¹ : ℝ≥0) half_le_one) := by
-- proof
  apply StatMech.Universality.fci_faceDualConfig_measurePreserving

/--
[fci_square_dichotomy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/FrameChangeIso.lean)
-/
@[path]
private lemma fci_square_dichotomy_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
-- given
  (hn : 0 ≤ n)
  (hnoH : ¬ HorizontalCrossing ω 0 n 0 n) :
-- imply
  (bcd_leftReach ω n).Finite ∧ (∀ {v w : Site 2}, v ∈ bcd_leftReach ω n → w ∈ rect 0 n 0 n → (hypercubicLattice 2).Adj v w → w ∉ bcd_leftReach ω n → (openSubgraph 2 (dualConfig ω)).Adj (rot90Fun v) (rot90Fun w)) ∧ (∃ f g : Site 2, (faceBoundaryGraph (bcd_leftReach ω n)).Adj f g) ∧ (∃ (u : Site 2) (c : (faceBoundaryGraph (bcd_leftReach ω n)).Walk u u), c.IsCycle ∧ (fci_faceWalk_to_dualWalk (bcd_leftReach ω n) c).IsCycle) := by
-- proof
  apply StatMech.Universality.fci_square_dichotomy ω n hn hnoH


-- created on 2026-10-23
