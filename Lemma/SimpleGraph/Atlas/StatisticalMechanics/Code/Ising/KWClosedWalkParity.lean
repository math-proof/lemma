import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Ising.KWClosedWalkParity.Part14
open Finset SimpleGraph StatMech StatMech.Ising


/--
[walkParity_eq_xor_of_isCoboundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWClosedWalkParity.lean)
-/
@[path]
private lemma walkParity_eq_xor_of_isCoboundary_eq
  [DecidableEq V]
  {Gp : SimpleGraph V}
  {δ : Finset (Sym2 V)}
  {c : V → Bool}
  {x y : V}
  {p : Gp.Walk x y}
-- given
  (hδ : ∀ {u v : V}, Gp.Adj u v → (s(u, v) ∈ δ ↔ c u ≠ c v)) :
-- imply
  walkParity Gp δ p = (c x).xor (c y) := by
-- proof
  apply StatMech.Ising.walkParity_eq_xor_of_isCoboundary c hδ p

/--
[evenOnCycles_of_isCoboundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWClosedWalkParity.lean)
-/
@[path]
private lemma evenOnCycles_of_isCoboundary_eq
  [DecidableEq V]
  {Gp : SimpleGraph V}
  [Fintype V]
  [DecidableRel Gp.Adj]
  {δ : Finset (Sym2 V)}
  {c : V → Bool}
-- given
  (hδ : ∀ {u v : V}, Gp.Adj u v → (s(u, v) ∈ δ ↔ c u ≠ c v)) :
-- imply
  EvenOnCycles Gp δ := by
-- proof
  apply StatMech.Ising.evenOnCycles_of_isCoboundary c hδ

/--
[cutEdges_isCoboundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWClosedWalkParity.lean)
-/
@[path]
private lemma cutEdges_isCoboundary_eq
  [DecidableEq V]
  {Gp : SimpleGraph V}
  [Fintype V]
  [DecidableRel Gp.Adj]
  {s : ConfigSpace V}
  {u v : V}
-- given
  (h : Gp.Adj u v) :
-- imply
  s(u, v) ∈ cutEdges Gp s ↔ s u ≠ s v := by
-- proof
  apply StatMech.Ising.cutEdges_isCoboundary s h

/--
[evenOnCycles_cutEdges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWClosedWalkParity.lean)
-/
@[path]
private lemma evenOnCycles_cutEdges_eq
  [DecidableEq V]
  {Gp : SimpleGraph V}
  [Fintype V]
  [DecidableRel Gp.Adj]
  {s : ConfigSpace V} :
-- imply
  EvenOnCycles Gp (cutEdges Gp s) := by
-- proof
  apply StatMech.Ising.evenOnCycles_cutEdges s

/--
[evenOnCycles_of_mem_cutSpace](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWClosedWalkParity.lean)
-/
@[path]
private lemma evenOnCycles_of_mem_cutSpace_eq
  [DecidableEq V]
  {Gp : SimpleGraph V}
  [Fintype V]
  [DecidableRel Gp.Adj]
  {δ : Finset (Sym2 V)}
-- given
  (hδ : δ ∈ cutSpace Gp) :
-- imply
  EvenOnCycles Gp δ := by
-- proof
  apply StatMech.Ising.evenOnCycles_of_mem_cutSpace hδ

/--
[evenOnCycles_iff_mem_cutSpace](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWClosedWalkParity.lean)
-/
@[path]
private lemma evenOnCycles_iff_mem_cutSpace_eq
  [Fintype V]
  [DecidableEq V]
  [Nonempty V]
  {δ : Finset (Sym2 V)}
-- given
  (hG : Gp.Preconnected)
  (hδsub : δ ⊆ Gp.edgeFinset) :
-- imply
  EvenOnCycles Gp δ ↔ δ ∈ cutSpace Gp := by
-- proof
  apply StatMech.Ising.evenOnCycles_iff_mem_cutSpace hG hδsub

/--
[isCoboundary_iff_mem_cutSpace](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWClosedWalkParity.lean)
-/
@[path]
private lemma isCoboundary_iff_mem_cutSpace_eq
  [Fintype V]
  [DecidableEq V]
  [Nonempty V]
  {δ : Finset (Sym2 V)}
-- given
  (hG : Gp.Preconnected)
  (hδsub : δ ⊆ Gp.edgeFinset) :
-- imply
  (∃ c : V → Bool, ∀ {u v : V}, Gp.Adj u v → (s(u, v) ∈ δ ↔ c u ≠ c v)) ↔ δ ∈ cutSpace Gp := by
-- proof
  apply StatMech.Ising.isCoboundary_iff_mem_cutSpace hG hδsub

/--
[closedDualWalkParity_of_sideColouring](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWClosedWalkParity.lean)
-/
@[path]
private lemma closedDualWalkParity_of_sideColouring_eq
  [Fintype V]
  [DecidableEq V]
  {ψ : Sym2 V ≃ Sym2 V}
-- given
  (hside : DualWalkHasSideColouring Gp Gd ψ) :
-- imply
  ClosedDualWalkParity Gp Gd ψ := by
-- proof
  apply StatMech.Ising.closedDualWalkParity_of_sideColouring ψ hside

/--
[even_to_cut_of_sideColouring](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWClosedWalkParity.lean)
-/
@[path]
private lemma even_to_cut_of_sideColouring_eq
  [Fintype V]
  [DecidableEq V]
  [Nonempty V]
  {ψ : Sym2 V ≃ Sym2 V}
-- given
  (hG : Gp.Preconnected)
  (hsymm : ∀ e ∈ Gd.edgeFinset, ψ.symm e ∈ Gp.edgeFinset)
  (hdecomp : EvenSubgraphWalkDecomp Gd)
  (hside : DualWalkHasSideColouring Gp Gd ψ) :
-- imply
  ∀ F ∈ evenSubgraphs Gd, (F.image ψ.symm) ∈ cutSpace Gp := by
-- proof
  apply StatMech.Ising.even_to_cut_of_sideColouring hG ψ hsymm hdecomp hside

/--
[dualWalkHasSideColouring_of_edgeless](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWClosedWalkParity.lean)
-/
@[path]
private lemma dualWalkHasSideColouring_of_edgeless_eq
  [Fintype V]
  [DecidableEq V]
  {ψ : Sym2 V ≃ Sym2 V}
-- given
  (hGd : Gd.edgeSet = ∅) :
-- imply
  DualWalkHasSideColouring Gp Gd ψ := by
-- proof
  apply StatMech.Ising.dualWalkHasSideColouring_of_edgeless ψ hGd

/--
[subgraphF_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWClosedWalkParity.lean)
-/
@[path]
private lemma subgraphF_adj_eq
  [Fintype V]
  [DecidableEq V]
  {F : Finset (Sym2 V)}
  {a b : V} :
-- imply
  (subgraphF F).Adj a b ↔ s(a,b) ∈ F ∧ a ≠ b := by
-- proof
  apply StatMech.Ising.subgraphF_adj F a b

/--
[mem_edgeSet_subgraphF](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWClosedWalkParity.lean)
-/
@[path]
private lemma mem_edgeSet_subgraphF_eq
  [Fintype V]
  [DecidableEq V]
  {F : Finset (Sym2 V)}
  {e : Sym2 V}
-- given
  (hF : ∀ e ∈ F, ¬ e.IsDiag) :
-- imply
  e ∈ (subgraphF F).edgeSet ↔ e ∈ F := by
-- proof
  apply StatMech.Ising.mem_edgeSet_subgraphF F hF e

/--
[degree_subgraphF_eq_incCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWClosedWalkParity.lean)
-/
@[path]
private lemma degree_subgraphF_eq_incCount_eq
  [Fintype V]
  [DecidableEq V]
  {F : Finset (Sym2 V)}
  {v : V}
-- given
  (hF : ∀ e ∈ F, ¬ e.IsDiag) :
-- imply
  (subgraphF F).degree v = incCount F v := by
-- proof
  apply StatMech.Ising.degree_subgraphF_eq_incCount F hF v

/--
[subgraphF_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWClosedWalkParity.lean)
-/
@[path]
private lemma subgraphF_even_eq
  [Fintype V]
  [DecidableEq V]
  {F : Finset (Sym2 V)}
  {v : V}
-- given
  (hF : ∀ e ∈ F, ¬ e.IsDiag)
  (hev : IsEvenSubgraph F) :
-- imply
  Even ((subgraphF F).degree v) := by
-- proof
  apply StatMech.Ising.subgraphF_even F hF hev v

/--
[compF_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWClosedWalkParity.lean)
-/
@[path]
private lemma compF_le_eq
  [Fintype V]
  [DecidableEq V]
  {F : Finset (Sym2 V)}
  {f : V} :
-- imply
  compF F f ≤ subgraphF F := by
-- proof
  apply StatMech.Ising.compF_le F f

/--
[compF_neighborSet_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWClosedWalkParity.lean)
-/
@[path]
private lemma compF_neighborSet_eq_eq
  [Fintype V]
  [DecidableEq V]
  {F : Finset (Sym2 V)}
  {f a : V}
-- given
  (ha : (subgraphF F).Reachable f a) :
-- imply
  (compF F f).neighborSet a = (subgraphF F).neighborSet a := by
-- proof
  apply StatMech.Ising.compF_neighborSet_eq F ha

/--
[compF_neighborSet_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWClosedWalkParity.lean)
-/
@[path]
private lemma compF_neighborSet_empty_eq
  [Fintype V]
  [DecidableEq V]
  {F : Finset (Sym2 V)}
  {f a : V}
-- given
  (ha : ¬ (subgraphF F).Reachable f a) :
-- imply
  (compF F f).neighborSet a = ∅ := by
-- proof
  apply StatMech.Ising.compF_neighborSet_empty F ha

/--
[compF_degree_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWClosedWalkParity.lean)
-/
@[path]
private lemma compF_degree_even_eq
  [Fintype V]
  [DecidableEq V]
  {F : Finset (Sym2 V)}
  {f a : V}
-- given
  (hF : ∀ e ∈ F, ¬ e.IsDiag)
  (hev : IsEvenSubgraph F) :
-- imply
  Even ((compF F f).degree a) := by
-- proof
  apply StatMech.Ising.compF_degree_even F hF hev f a

/--
[mem_compSuppF](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWClosedWalkParity.lean)
-/
@[path]
private lemma mem_compSuppF_eq
  [Fintype V]
  [DecidableEq V]
  {F : Finset (Sym2 V)}
  {f g : V} :
-- imply
  g ∈ compSuppF F f ↔ (subgraphF F).Reachable f g := by
-- proof
  apply StatMech.Ising.mem_compSuppF F

/--
[self_mem_compSuppF](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWClosedWalkParity.lean)
-/
@[path]
private lemma self_mem_compSuppF_eq
  [Fintype V]
  [DecidableEq V]
  {F : Finset (Sym2 V)}
  {f : V} :
-- imply
  f ∈ compSuppF F f := by
-- proof
  apply StatMech.Ising.self_mem_compSuppF F f

/--
[compF_support_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWClosedWalkParity.lean)
-/
@[path]
private lemma compF_support_subset_eq
  [Fintype V]
  [DecidableEq V]
  {F : Finset (Sym2 V)}
  {f : V} :
-- imply
  (compF F f).support ⊆ (compSuppF F f : Set V) := by
-- proof
  apply StatMech.Ising.compF_support_subset F f

/--
[compF_edge_of_walk_from_base](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWClosedWalkParity.lean)
-/
@[path]
private lemma compF_edge_of_walk_from_base_eq
  [Fintype V]
  [DecidableEq V]
  {F : Finset (Sym2 V)}
  {f g : V}
  {q : (subgraphF F).Walk f g}
  {e : Sym2 V}
-- given
  (he : e ∈ q.edges) :
-- imply
  e ∈ (compF F f).edgeSet := by
-- proof
  apply StatMech.Ising.compF_edge_of_walk_from_base F q he

/--
[compF_reachable_of_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWClosedWalkParity.lean)
-/
@[path]
private lemma compF_reachable_of_reachable_eq
  [Fintype V]
  [DecidableEq V]
  {F : Finset (Sym2 V)}
  {f g : V}
-- given
  (h : (subgraphF F).Reachable f g) :
-- imply
  (compF F f).Reachable f g := by
-- proof
  apply StatMech.Ising.compF_reachable_of_reachable F h

/--
[compF_walk_in_compSuppF](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWClosedWalkParity.lean)
-/
@[path]
private lemma compF_walk_in_compSuppF_eq
  [Fintype V]
  [DecidableEq V]
  {F : Finset (Sym2 V)}
  {f : V}
  {g : V}
  {p : (compF F f).Walk f g} :
-- imply
  ∀ v ∈ p.support, v ∈ compSuppF F f := by
-- proof
  apply StatMech.Ising.compF_walk_in_compSuppF F p

/--
[reachable_induce_of_walk_in_set'](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWClosedWalkParity.lean)
-/
@[path]
private lemma reachable_induce_of_walk_in_set'_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {S : Set V}
  {a b : V}
  {p : G.Walk a b}
-- given
  (hsub : ∀ v ∈ p.support, v ∈ S)
  (ha : a ∈ S) :
-- imply
  (G.induce S).Reachable ⟨a, ha⟩ ⟨b, hsub b p.end_mem_support⟩ := by
-- proof
  apply StatMech.Ising.reachable_induce_of_walk_in_set' p hsub ha

/--
[compF_induce_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWClosedWalkParity.lean)
-/
@[path]
private lemma compF_induce_connected_eq
  [Fintype V]
  [DecidableEq V]
  {F : Finset (Sym2 V)}
  {f : V} :
-- imply
  ((compF F f).induce (compSuppF F f : Set V)).Connected := by
-- proof
  apply StatMech.Ising.compF_induce_connected F f

/--
[compF_eulerCircuit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWClosedWalkParity.lean)
-/
@[path]
private lemma compF_eulerCircuit_eq
  [Fintype V]
  [DecidableEq V]
  {F : Finset (Sym2 V)}
  {f : V}
-- given
  (hF : ∀ e ∈ F, ¬ e.IsDiag)
  (hev : IsEvenSubgraph F) :
-- imply
  ∃ c : (compF F f).Walk f f, ∀ e ∈ (compF F f).edgeSet, e ∈ c.edges := by
-- proof
  apply StatMech.Ising.compF_eulerCircuit F hF hev f

/--
[mem_compF_edgeSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWClosedWalkParity.lean)
-/
@[path]
private lemma mem_compF_edgeSet_eq
  [Fintype V]
  [DecidableEq V]
  {F : Finset (Sym2 V)}
  {f : V}
  {e : Sym2 V}
-- given
  (hF : ∀ e ∈ F, ¬ e.IsDiag) :
-- imply
  e ∈ (compF F f).edgeSet ↔ (e ∈ F ∧ ∀ x ∈ e, (subgraphF F).Reachable f x) := by
-- proof
  apply StatMech.Ising.mem_compF_edgeSet F hF f e

/--
[compEulerWalk_cov](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWClosedWalkParity.lean)
-/
@[path]
private lemma compEulerWalk_cov_eq
  [Fintype V]
  [DecidableEq V]
  {F : Finset (Sym2 V)}
  {f : V}
-- given
  (hF : ∀ e ∈ F, ¬ e.IsDiag)
  (hev : IsEvenSubgraph F) :
-- imply
  ∀ e ∈ (compF F f).edgeSet, e ∈ (compEulerWalk F hF hev f).edges := by
-- proof
  apply StatMech.Ising.compEulerWalk_cov F hF hev f

/--
[compEulerWalk_edges_toFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWClosedWalkParity.lean)
-/
@[path]
private lemma compEulerWalk_edges_toFinset_eq
  [Fintype V]
  [DecidableEq V]
  {F : Finset (Sym2 V)}
  {f : V}
-- given
  (hF : ∀ e ∈ F, ¬ e.IsDiag)
  (hev : IsEvenSubgraph F) :
-- imply
  ((compEulerWalk F hF hev f).edges.toFinset : Finset (Sym2 V)) = F.filter (fun e => ∀ x ∈ e, (subgraphF F).Reachable f x) := by
-- proof
  apply StatMech.Ising.compEulerWalk_edges_toFinset F hF hev f

/--
[edge_reachable_from_out](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWClosedWalkParity.lean)
-/
@[path]
private lemma edge_reachable_from_out_eq
  [Fintype V]
  [DecidableEq V]
  {V : Type}
  [Fintype V]
  [DecidableEq V]
  {F : Finset (Sym2 V)}
  {x y : V}
-- given
  (hF : ∀ e ∈ F, ¬ e.IsDiag)
  (hmem : s(x, y) ∈ F) :
-- imply
  ∀ z ∈ s(x, y), (subgraphF F).Reachable ((subgraphF F).connectedComponentMk x).out z := by
-- proof
  apply StatMech.Ising.edge_reachable_from_out F hF hmem

/--
[evenSubgraph_decomp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWClosedWalkParity.lean)
-/
@[path]
private lemma evenSubgraph_decomp_eq
  [Fintype V]
  [DecidableEq V]
  {V : Type}
  [Fintype V]
  [DecidableEq V]
  {F : Finset (Sym2 V)}
-- given
  (hF : ∀ e ∈ F, ¬ e.IsDiag)
  (hev : IsEvenSubgraph F) :
-- imply
  ∃ (ι : Type) (_ : DecidableEq ι) (s : Finset ι) (w : ι → V) (W : (i : ι) → (subgraphF F).Walk (w i) (w i)), F = s.biUnion (fun i => (W i).edges.toFinset) ∧ (s : Set ι).PairwiseDisjoint (fun i => (W i).edges.toFinset) := by
-- proof
  apply StatMech.Ising.evenSubgraph_decomp F hF hev

/--
[subgraphF_le_of_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWClosedWalkParity.lean)
-/
@[path]
private lemma subgraphF_le_of_subset_eq
  [Fintype V]
  [DecidableEq V]
  {V : Type}
  [Fintype V]
  [DecidableEq V]
  {Gd : SimpleGraph V}
  [DecidableRel Gd.Adj]
  {F : Finset (Sym2 V)}
-- given
  (hFsub : F ⊆ Gd.edgeFinset) :
-- imply
  subgraphF F ≤ Gd := by
-- proof
  apply StatMech.Ising.subgraphF_le_of_subset hFsub

/--
[evenSubgraphs_no_diag](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWClosedWalkParity.lean)
-/
@[path]
private lemma evenSubgraphs_no_diag_eq
  [Fintype V]
  [DecidableEq V]
  {V : Type}
  [Fintype V]
  [DecidableEq V]
  {Gd : SimpleGraph V}
  [DecidableRel Gd.Adj]
  {F : Finset (Sym2 V)}
  {e : Sym2 V}
-- given
  (hFsub : F ⊆ Gd.edgeFinset)
  (he : e ∈ F) :
-- imply
  ¬ e.IsDiag := by
-- proof
  apply StatMech.Ising.evenSubgraphs_no_diag hFsub e he

/--
[edges_mapLe_toFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWClosedWalkParity.lean)
-/
@[path]
private lemma edges_mapLe_toFinset_eq
  [Fintype V]
  [DecidableEq V]
  {V : Type}
  [Fintype V]
  [DecidableEq V]
  {G H : SimpleGraph V}
  {a b : V}
  {p : G.Walk a b}
-- given
  (h : G ≤ H) :
-- imply
  (p.mapLe h).edges.toFinset = p.edges.toFinset := by
-- proof
  apply StatMech.Ising.edges_mapLe_toFinset h p

/--
[evenSubgraphWalkDecomp_general](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWClosedWalkParity.lean)
-/
@[path]
private lemma evenSubgraphWalkDecomp_general_eq
  [Fintype V]
  [DecidableEq V]
  {V : Type}
  [Fintype V]
  [DecidableEq V]
  {Gd : SimpleGraph V}
  [DecidableRel Gd.Adj] :
-- imply
  EvenSubgraphWalkDecomp Gd := by
-- proof
  apply StatMech.Ising.evenSubgraphWalkDecomp_general Gd

/--
[mem_regionBoundary_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWClosedWalkParity.lean)
-/
@[path]
private lemma mem_regionBoundary_iff_eq
  [Fintype V]
  [DecidableEq V]
  {S : V → Bool}
  {u v : V}
-- given
  (h : Gp.Adj u v) :
-- imply
  s(u, v) ∈ regionBoundary Gp S ↔ S u ≠ S v := by
-- proof
  apply StatMech.Ising.mem_regionBoundary_iff S h

/--
[evenOnCycles_regionBoundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWClosedWalkParity.lean)
-/
@[path]
private lemma evenOnCycles_regionBoundary_eq
  [Fintype V]
  [DecidableEq V]
  {S : V → Bool} :
-- imply
  EvenOnCycles Gp (regionBoundary Gp S) := by
-- proof
  apply StatMech.Ising.evenOnCycles_regionBoundary S

/--
[dualWalkBoundsRegion_isSideColouring](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWClosedWalkParity.lean)
-/
@[path]
private lemma dualWalkBoundsRegion_isSideColouring_eq
  [Fintype V]
  [DecidableEq V]
  {ψ : Sym2 V ≃ Sym2 V}
-- given
  (hreg : DualWalkBoundsRegion Gp Gd ψ) :
-- imply
  DualWalkHasSideColouring Gp Gd ψ := by
-- proof
  apply StatMech.Ising.dualWalkBoundsRegion_isSideColouring ψ hreg

/--
[closedDualWalkParity_of_boundsRegion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWClosedWalkParity.lean)
-/
@[path]
private lemma closedDualWalkParity_of_boundsRegion_eq
  [Fintype V]
  [DecidableEq V]
  {ψ : Sym2 V ≃ Sym2 V}
-- given
  (hreg : DualWalkBoundsRegion Gp Gd ψ) :
-- imply
  ClosedDualWalkParity Gp Gd ψ := by
-- proof
  apply StatMech.Ising.closedDualWalkParity_of_boundsRegion ψ hreg

/--
[even_to_cut_of_boundsRegion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWClosedWalkParity.lean)
-/
@[path]
private lemma even_to_cut_of_boundsRegion_eq
  [Fintype V]
  [DecidableEq V]
  [Nonempty V]
  {ψ : Sym2 V ≃ Sym2 V}
-- given
  (hG : Gp.Preconnected)
  (hsymm : ∀ e ∈ Gd.edgeFinset, ψ.symm e ∈ Gp.edgeFinset)
  (hdecomp : EvenSubgraphWalkDecomp Gd)
  (hreg : DualWalkBoundsRegion Gp Gd ψ) :
-- imply
  ∀ F ∈ evenSubgraphs Gd, (F.image ψ.symm) ∈ cutSpace Gp := by
-- proof
  apply StatMech.Ising.even_to_cut_of_boundsRegion hG ψ hsymm hdecomp hreg

/--
[dualWalkBoundsRegion_of_edgeless](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWClosedWalkParity.lean)
-/
@[path]
private lemma dualWalkBoundsRegion_of_edgeless_eq
  [Fintype V]
  [DecidableEq V]
  {ψ : Sym2 V ≃ Sym2 V}
-- given
  (hGd : Gd.edgeSet = ∅) :
-- imply
  DualWalkBoundsRegion Gp Gd ψ := by
-- proof
  apply StatMech.Ising.dualWalkBoundsRegion_of_edgeless ψ hGd

/--
[latticeSide_eq_true](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWClosedWalkParity.lean)
-/
@[path]
private lemma latticeSide_eq_true_eq
  {S : Set (Site 2)}
  {x : Site 2} :
-- imply
  latticeSide S x = true ↔ x ∈ S := by
-- proof
  apply StatMech.Ising.latticeSide_eq_true

/--
[crossCount_even_iff_latticeSide](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWClosedWalkParity.lean)
-/
@[path]
private lemma crossCount_even_iff_latticeSide_eq
  {S : Set (Site 2)}
  {x y : Site 2}
  {w : (hypercubicLattice 2).Walk x y} :
-- imply
  Even (crossCount S w) ↔ latticeSide S x = latticeSide S y := by
-- proof
  apply StatMech.Ising.crossCount_even_iff_latticeSide S w

/--
[latticeRegionBoundary_evenOnLoop](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWClosedWalkParity.lean)
-/
@[path]
private lemma latticeRegionBoundary_evenOnLoop_eq
  {S : Set (Site 2)}
  {x : Site 2}
  {w : (hypercubicLattice 2).Walk x x} :
-- imply
  Even (crossCount S w) := by
-- proof
  apply StatMech.Ising.latticeRegionBoundary_evenOnLoop S w

/--
[latticeSide_isRegion_of_pullback_eq_bdEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWClosedWalkParity.lean)
-/
@[path]
private lemma latticeSide_isRegion_of_pullback_eq_bdEdge_eq
  {Gd : SimpleGraph (Site 2)}
  [DecidableRel Gd.Adj]
  {ψ : Sym2 (Site 2) ≃ Sym2 (Site 2)}
  {S : Set (Site 2)}
  {w : Site 2}
  {W : Gd.Walk w w}
-- given
  (hpull : ∀ {u v : Site 2}, (hypercubicLattice 2).Adj u v → (s(u, v) ∈ (W.edges.toFinset).image ψ.symm ↔ bdEdge S s(u, v))) :
-- imply
  ∀ {u v : Site 2}, (hypercubicLattice 2).Adj u v → (s(u, v) ∈ (W.edges.toFinset).image ψ.symm ↔ latticeSide S u ≠ latticeSide S v) := by
-- proof
  apply StatMech.Ising.latticeSide_isRegion_of_pullback_eq_bdEdge ψ S W hpull

/--
[even_to_cut_of_boundsRegion'](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWClosedWalkParity.lean)
-/
@[path]
private lemma even_to_cut_of_boundsRegion'_eq
  {V : Type}
  [Fintype V]
  [DecidableEq V]
  [Nonempty V]
  {ψ : Sym2 V ≃ Sym2 V}
-- given
  (hG : Gp.Preconnected)
  (hsymm : ∀ e ∈ Gd.edgeFinset, ψ.symm e ∈ Gp.edgeFinset)
  (hreg : DualWalkBoundsRegion Gp Gd ψ) :
-- imply
  ∀ F ∈ evenSubgraphs Gd, (F.image ψ.symm) ∈ cutSpace Gp := by
-- proof
  apply StatMech.Ising.even_to_cut_of_boundsRegion' hG ψ hsymm hreg

/--
[isingZ_self_dual_of_boundsRegion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWClosedWalkParity.lean)
-/
@[path]
private lemma isingZ_self_dual_of_boundsRegion_eq
  {V : Type}
  [Fintype V]
  [DecidableEq V]
  [Nonempty V]
  {ψ : Sym2 V ≃ Sym2 V}
  {β βstar : ℝ}
-- given
  (hG : Gp.Preconnected)
  (hedge : ∀ e ∈ Gp.edgeFinset, ψ e ∈ Gd.edgeFinset)
  (hsymm : ∀ e ∈ Gd.edgeFinset, ψ.symm e ∈ Gp.edgeFinset)
  (hfwd : ∀ δ ∈ cutSpace Gp, IsEvenSubgraph (δ.image ψ))
  (hreg : DualWalkBoundsRegion Gp Gd ψ)
  (htemp : Real.tanh βstar = Real.exp (-2 * β)) :
-- imply
  isingZ Gd βstar 0 = ((2 : ℝ) ^ Fintype.card V * (Real.cosh βstar) ^ Gd.edgeFinset.card / (Real.exp (β * Gp.edgeFinset.card) * 2)) * isingZ Gp β 0 := by
-- proof
  apply StatMech.Ising.isingZ_self_dual_of_boundsRegion hG ψ hedge hsymm hfwd hreg β βstar htemp


-- created on 2026-10-23
