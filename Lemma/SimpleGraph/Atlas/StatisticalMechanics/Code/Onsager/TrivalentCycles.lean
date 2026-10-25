import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Onsager.TrivalentCycles
open StatMech StatMech.Onsager


/--
[ons_evenSubgraph_disjoint_diag](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TrivalentCycles.lean)
-/
@[path]
private lemma ons_evenSubgraph_disjoint_diag_eq
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {F : Finset (Sym2 V)}
-- given
  (hFsub : F ⊆ G.edgeFinset) :
-- imply
  Disjoint (F : Set (Sym2 V)) Sym2.diagSet := by
-- proof
  apply StatMech.Onsager.ons_evenSubgraph_disjoint_diag F hFsub

/--
[ons_edgeSubgraph_edgeSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TrivalentCycles.lean)
-/
@[path]
private lemma ons_edgeSubgraph_edgeSet_eq
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {F : Finset (Sym2 V)}
-- given
  (hFsub : F ⊆ G.edgeFinset) :
-- imply
  (ons_edgeSubgraph F).edgeSet = (F : Set (Sym2 V)) := by
-- proof
  apply StatMech.Onsager.ons_edgeSubgraph_edgeSet F hFsub

/--
[ons_edgeSubgraph_edgeFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TrivalentCycles.lean)
-/
@[path]
private lemma ons_edgeSubgraph_edgeFinset_eq
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {F : Finset (Sym2 V)}
-- given
  (hFsub : F ⊆ G.edgeFinset) :
-- imply
  (ons_edgeSubgraph F).edgeFinset = F := by
-- proof
  apply StatMech.Onsager.ons_edgeSubgraph_edgeFinset F hFsub

/--
[ons_incCount_eq_edgeSubgraph_degree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TrivalentCycles.lean)
-/
@[path]
private lemma ons_incCount_eq_edgeSubgraph_degree_eq
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {F : Finset (Sym2 V)}
  {v : V}
-- given
  (hFsub : F ⊆ G.edgeFinset) :
-- imply
  incCount F v = (ons_edgeSubgraph F).degree v := by
-- proof
  apply StatMech.Onsager.ons_incCount_eq_edgeSubgraph_degree F hFsub v

/--
[ons_edgeSubgraph_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TrivalentCycles.lean)
-/
@[path]
private lemma ons_edgeSubgraph_le_eq
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {F : Finset (Sym2 V)}
-- given
  (hFsub : F ⊆ G.edgeFinset) :
-- imply
  ons_edgeSubgraph F ≤ G := by
-- proof
  apply StatMech.Onsager.ons_edgeSubgraph_le F hFsub

/--
[ons_isCycles_of_trivalent_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TrivalentCycles.lean)
-/
@[path]
private lemma ons_isCycles_of_trivalent_even_eq
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {F : Finset (Sym2 V)}
-- given
  (hdeg : ∀ v, G.degree v ≤ 3)
  (hF : F ∈ evenSubgraphs G) :
-- imply
  (ons_edgeSubgraph F).IsCycles := by
-- proof
  apply StatMech.Onsager.ons_isCycles_of_trivalent_even hdeg F hF

/--
[ons_trivalent_even_component_cycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TrivalentCycles.lean)
-/
@[path]
private lemma ons_trivalent_even_component_cycle_eq
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {F : Finset (Sym2 V)}
  {c : (ons_edgeSubgraph F).ConnectedComponent}
  {v : V}
-- given
  (hdeg : ∀ v, G.degree v ≤ 3)
  (hF : F ∈ evenSubgraphs G)
  (hv : v ∈ c.supp)
  (hn : ((ons_edgeSubgraph F).neighborSet v).Nonempty) :
-- imply
  ∃ p : (ons_edgeSubgraph F).Walk v v, p.IsCycle ∧ p.toSubgraph.verts = c.supp := by
-- proof
  apply StatMech.Onsager.ons_trivalent_even_component_cycle hdeg F hF c hv hn

/--
[ons_trivalent_even_exists_cycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TrivalentCycles.lean)
-/
@[path]
private lemma ons_trivalent_even_exists_cycle_eq
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {F : Finset (Sym2 V)}
-- given
  (hdeg : ∀ v, G.degree v ≤ 3)
  (hF : F ∈ evenSubgraphs G)
  (hne : F.Nonempty) :
-- imply
  ∃ (v : V) (p : G.Walk v v), p.IsCycle ∧ p.edges.toFinset ⊆ F := by
-- proof
  apply StatMech.Onsager.ons_trivalent_even_exists_cycle hdeg F hF hne

/--
[ons_cycle_edges_evenSubgraph](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TrivalentCycles.lean)
-/
@[path]
private lemma ons_cycle_edges_evenSubgraph_eq
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {v : V}
  {p : G.Walk v v}
-- given
  (hp : p.IsCycle) :
-- imply
  p.edges.toFinset ∈ evenSubgraphs G := by
-- proof
  apply StatMech.Onsager.ons_cycle_edges_evenSubgraph p hp

/--
[ons_trivalent_even_cycle_decomposition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TrivalentCycles.lean)
-/
@[path]
private lemma ons_trivalent_even_cycle_decomposition_eq
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {F : Finset (Sym2 V)}
-- given
  (hdeg : ∀ v, G.degree v ≤ 3)
  (hF : F ∈ evenSubgraphs G) :
-- imply
  ∃ (ι : Type u) (_ : Fintype ι) (_ : DecidableEq ι) (base : ι → V) (p : (i : ι) → G.Walk (base i) (base i)), (∀ i, (p i).IsCycle) ∧ F = Finset.univ.biUnion (fun i => (p i).edges.toFinset) ∧ ((Finset.univ : Finset ι) : Set ι).PairwiseDisjoint (fun i => (p i).edges.toFinset) ∧ ((Finset.univ : Finset ι) : Set ι).PairwiseDisjoint (fun i => (p i).toSubgraph.verts) := by
-- proof
  apply StatMech.Onsager.ons_trivalent_even_cycle_decomposition hdeg F hF


-- created on 2026-10-23
