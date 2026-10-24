import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Percolation.FiniteTreeTripod
open Set SimpleGraph Finset StatMech StatMech.Percolation


/--
[ftt_tree_two_leaves](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/FiniteTreeTripod.lean)
-/
@[path]
private lemma ftt_tree_two_leaves_eq
  [Fintype V]
  {T : SimpleGraph V}
  [DecidableRel T.Adj]
-- given
  (hT : T.IsTree)
  (hn : 2 ≤ Fintype.card V) :
-- imply
  ∃ a b : V, a ≠ b ∧ T.degree a = 1 ∧ T.degree b = 1 := by
-- proof
  apply StatMech.Percolation.ftt_tree_two_leaves T hT hn

/--
[ftt_branch_vertex_of_three_leaves](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/FiniteTreeTripod.lean)
-/
@[path]
private lemma ftt_branch_vertex_of_three_leaves_eq
  [Fintype V]
  [DecidableEq V]
  {T : SimpleGraph V}
  [DecidableRel T.Adj]
  {a b c : V}
-- given
  (hT : T.IsTree)
  (hab : a ≠ b)
  (hac : a ≠ c)
  (hbc : b ≠ c)
  (ha : T.degree a = 1)
  (hb : T.degree b = 1)
  (hc : T.degree c = 1) :
-- imply
  ∃ u : V, 3 ≤ T.degree u := by
-- proof
  apply StatMech.Percolation.ftt_branch_vertex_of_three_leaves T hT hab hac hbc ha hb hc

/--
[ftt_not_mem_support_of_isolated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/FiniteTreeTripod.lean)
-/
@[path]
private lemma ftt_not_mem_support_of_isolated_eq
  {G : SimpleGraph V}
  {u : V}
-- given
  (hiso : ∀ z, ¬ G.Adj u z) :
-- imply
  ∀ {a b : V} (w : G.Walk a b), a ≠ u → u ∉ w.support := by
-- proof
  apply StatMech.Percolation.ftt_not_mem_support_of_isolated hiso

/--
[ftt_neighbors_separated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/FiniteTreeTripod.lean)
-/
@[path]
private lemma ftt_neighbors_separated_eq
  {G : SimpleGraph V}
  {u a b : V}
-- given
  (hG : G.IsAcyclic)
  (hua : G.Adj u a)
  (hub : G.Adj u b)
  (hab : a ≠ b) :
-- imply
  ¬ (G.deleteIncidenceSet u).Reachable a b := by
-- proof
  apply StatMech.Percolation.ftt_neighbors_separated G hG hua hub hab

/--
[ftt_leaf_in_neighbor_branch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/FiniteTreeTripod.lean)
-/
@[path]
private lemma ftt_leaf_in_neighbor_branch_eq
  [Fintype V]
  [DecidableEq V]
  {T : SimpleGraph V}
  [DecidableRel T.Adj]
  {u v : V}
-- given
  (hT : T.IsTree)
  (huv : T.Adj u v) :
-- imply
  ∃ l : V, T.degree l = 1 ∧ (T.deleteIncidenceSet u).Reachable v l := by
-- proof
  apply StatMech.Percolation.ftt_leaf_in_neighbor_branch T hT huv

/--
[ftt_finite_tree_tripod](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/FiniteTreeTripod.lean)
-/
@[path]
private lemma ftt_finite_tree_tripod_eq
  [Fintype V]
  [DecidableEq V]
  {T : SimpleGraph V}
  [DecidableRel T.Adj]
  {u : V}
-- given
  (hT : T.IsTree)
  (hu : 3 ≤ T.degree u) :
-- imply
  ∃ l : Fin 3 → V, Function.Injective l ∧ (∀ i, T.degree (l i) = 1) ∧ (∀ i j, i ≠ j → ¬ (T.deleteIncidenceSet u).Reachable (l i) (l j)) := by
-- proof
  apply StatMech.Percolation.ftt_finite_tree_tripod T hT hu

/--
[ftt_finite_tree_tripod_with_stems](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/FiniteTreeTripod.lean)
-/
@[path]
private lemma ftt_finite_tree_tripod_with_stems_eq
  [Fintype V]
  [DecidableEq V]
  {T : SimpleGraph V}
  [DecidableRel T.Adj]
  {u : V}
-- given
  (hT : T.IsTree)
  (hu : 3 ≤ T.degree u) :
-- imply
  ∃ stem leaf : Fin 3 → V, Function.Injective stem ∧ (∀ i, T.Adj u (stem i)) ∧ Function.Injective leaf ∧ (∀ i, T.degree (leaf i) = 1) ∧ (∀ i, (T.deleteIncidenceSet u).Reachable (stem i) (leaf i)) ∧ (∀ i j, i ≠ j → ¬ (T.deleteIncidenceSet u).Reachable (leaf i) (leaf j)) := by
-- proof
  apply StatMech.Percolation.ftt_finite_tree_tripod_with_stems T hT hu


-- created on 2026-10-23
