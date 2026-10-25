import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Lattice.JordanContour.Part3
open Finset Set SimpleGraph Function StatMech StatMech.Lattice


/--
[walk_induce_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanContour.lean)
-/
@[path]
private lemma walk_induce_reachable_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {G : SimpleGraph V}
  {s : Set V}
  {x y : V}
  {w : G.Walk x y}
-- given
  (hw : ∀ z ∈ w.support, z ∈ s)
  (hx : x ∈ s)
  (hy : y ∈ s) :
-- imply
  (G.induce s).Reachable ⟨x, hx⟩ ⟨y, hy⟩ := by
-- proof
  apply StatMech.Lattice.walk_induce_reachable G s w hw hx hy

/--
[latticeMinusBarrier_adj_of_both_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanContour.lean)
-/
@[path]
private lemma latticeMinusBarrier_adj_of_both_mem_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {S : Set (Site 2)}
  {x y : Site 2}
-- given
  (hadj : (hypercubicLattice 2).Adj x y)
  (hx : x ∈ S)
  (hy : y ∈ S) :
-- imply
  (latticeMinusBarrier S).Adj x y := by
-- proof
  apply StatMech.Lattice.latticeMinusBarrier_adj_of_both_mem S hadj hx hy

/--
[latticeMinusBarrier_adj_of_both_not_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanContour.lean)
-/
@[path]
private lemma latticeMinusBarrier_adj_of_both_not_mem_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {S : Set (Site 2)}
  {x y : Site 2}
-- given
  (hadj : (hypercubicLattice 2).Adj x y)
  (hx : x ∉ S)
  (hy : y ∉ S) :
-- imply
  (latticeMinusBarrier S).Adj x y := by
-- proof
  apply StatMech.Lattice.latticeMinusBarrier_adj_of_both_not_mem S hadj hx hy

/--
[openWalk_support_mem_cluster](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanContour.lean)
-/
@[path]
private lemma openWalk_support_mem_cluster_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {o : Site 2}
  {y : Site 2}
  {w : (openSubgraph 2 ω).Walk o y} :
-- imply
  ∀ z ∈ w.support, z ∈ cluster 2 ω o := by
-- proof
  apply StatMech.Lattice.openWalk_support_mem_cluster o w

/--
[cluster_reachable_in_barrier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanContour.lean)
-/
@[path]
private lemma cluster_reachable_in_barrier_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {o : Site 2}
  {x y : Site 2}
-- given
  (hx : x ∈ cluster 2 ω o)
  (hy : y ∈ cluster 2 ω o) :
-- imply
  (latticeMinusBarrier (cluster 2 ω o)).Reachable x y := by
-- proof
  apply StatMech.Lattice.cluster_reachable_in_barrier o hx hy

/--
[insideComponent_supp_subset_cluster](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanContour.lean)
-/
@[path]
private lemma insideComponent_supp_subset_cluster_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {o : Site 2} :
-- imply
  ((latticeMinusBarrier (cluster 2 ω o)).connectedComponentMk o).supp ⊆ cluster 2 ω o := by
-- proof
  apply StatMech.Lattice.insideComponent_supp_subset_cluster o

/--
[insideComponent_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanContour.lean)
-/
@[path]
private lemma insideComponent_finite_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {o : Site 2}
-- given
  (hfin : (cluster 2 ω o).Finite) :
-- imply
  ((latticeMinusBarrier (cluster 2 ω o)).connectedComponentMk o).supp.Finite := by
-- proof
  apply StatMech.Lattice.insideComponent_finite o hfin

/--
[exterior_reachable_in_barrier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanContour.lean)
-/
@[path]
private lemma exterior_reachable_in_barrier_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {K : Set (Site 2)}
  {R : ℕ}
  {x y : Site 2}
-- given
  (hK : K ⊆ box 2 R)
  (hx : x ∈ exterior 2 R)
  (hy : y ∈ exterior 2 R) :
-- imply
  (latticeMinusBarrier K).Reachable x y := by
-- proof
  apply StatMech.Lattice.exterior_reachable_in_barrier K R hK hx hy

/--
[outsideComponent_infinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanContour.lean)
-/
@[path]
private lemma outsideComponent_infinite_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {K : Set (Site 2)}
  {R : ℕ}
-- given
  (hK : K ⊆ box 2 R) :
-- imply
  ((latticeMinusBarrier K).connectedComponentMk (beacon 2 R)).supp.Infinite := by
-- proof
  apply StatMech.Lattice.outsideComponent_infinite K R hK

/--
[cluster_inside_not_reachable_outside](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanContour.lean)
-/
@[path]
private lemma cluster_inside_not_reachable_outside_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {o : Site 2}
  {x y : Site 2}
-- given
  (hx : x ∈ cluster 2 ω o)
  (hy : y ∉ cluster 2 ω o) :
-- imply
  ¬ (latticeMinusBarrier (cluster 2 ω o)).Reachable x y := by
-- proof
  apply StatMech.Lattice.cluster_inside_not_reachable_outside o hx hy

/--
[inside_ne_outside_component](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanContour.lean)
-/
@[path]
private lemma inside_ne_outside_component_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {o : Site 2}
  {R : ℕ}
-- given
  (hR : cluster 2 ω o ⊆ box 2 R) :
-- imply
  (latticeMinusBarrier (cluster 2 ω o)).connectedComponentMk o ≠ (latticeMinusBarrier (cluster 2 ω o)).connectedComponentMk (beacon 2 R) := by
-- proof
  apply StatMech.Lattice.inside_ne_outside_component o R hR

/--
[barrier_sameSide_of_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanContour.lean)
-/
@[path]
private lemma barrier_sameSide_of_reachable_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {S : Set (Site 2)}
  {x y : Site 2}
-- given
  (h : (latticeMinusBarrier S).Reachable x y) :
-- imply
  (x ∈ S ↔ y ∈ S) := by
-- proof
  apply StatMech.Lattice.barrier_sameSide_of_reachable S h

/--
[barrier_separates](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanContour.lean)
-/
@[path]
private lemma barrier_separates_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {S : Set (Site 2)} :
-- imply
  (∀ ⦃x y : Site 2⦄, (latticeMinusBarrier S).Reachable x y → (x ∈ S ↔ y ∈ S)) ∧ (∀ ⦃x y : Site 2⦄, x ∈ S → y ∉ S → ¬ (latticeMinusBarrier S).Reachable x y) := by
-- proof
  apply StatMech.Lattice.barrier_separates S

/--
[discrete_jordan_separation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanContour.lean)
-/
@[path]
private lemma discrete_jordan_separation_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {o : Site 2}
-- given
  (hfin : (cluster 2 ω o).Finite) :
-- imply
  ∃ R : ℕ, cluster 2 ω o ⊆ box 2 R ∧ (∀ ⦃x y : Site 2⦄, x ∈ cluster 2 ω o → y ∈ cluster 2 ω o → (latticeMinusBarrier (cluster 2 ω o)).Reachable x y) ∧ (∀ ⦃x y : Site 2⦄, x ∈ exterior 2 R → y ∈ exterior 2 R → (latticeMinusBarrier (cluster 2 ω o)).Reachable x y) ∧ (∀ ⦃x y : Site 2⦄, x ∈ cluster 2 ω o → y ∉ cluster 2 ω o → ¬ (latticeMinusBarrier (cluster 2 ω o)).Reachable x y) := by
-- proof
  apply StatMech.Lattice.discrete_jordan_separation o hfin

/--
[discrete_jordan_components](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanContour.lean)
-/
@[path]
private lemma discrete_jordan_components_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {o : Site 2}
-- given
  (hfin : (cluster 2 ω o).Finite) :
-- imply
  ∃ (R : ℕ) (_ : cluster 2 ω o ⊆ box 2 R) (Cin Cout : (latticeMinusBarrier (cluster 2 ω o)).ConnectedComponent), Cin = (latticeMinusBarrier (cluster 2 ω o)).connectedComponentMk o ∧ Cout = (latticeMinusBarrier (cluster 2 ω o)).connectedComponentMk (beacon 2 R) ∧ Cin.supp.Finite ∧ Cout.supp.Infinite ∧ Cin ≠ Cout ∧ cluster 2 ω o ⊆ Cin.supp ∧ exterior 2 R ⊆ Cout.supp := by
-- proof
  apply StatMech.Lattice.discrete_jordan_components o hfin


-- created on 2026-10-23
