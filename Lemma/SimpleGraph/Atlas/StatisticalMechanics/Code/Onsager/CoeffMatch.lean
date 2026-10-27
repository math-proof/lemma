import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Onsager.CoeffMatch
open Finset SimpleGraph StatMech StatMech.Onsager


/--
[ons_X_eq_sum_evenSubgraphs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CoeffMatch.lean)
-/
@[path]
private lemma ons_X_eq_sum_evenSubgraphs_eq
  {V : Type}
  [Fintype V]
  [DecidableEq V]
  {x : ℝ} :
-- imply
  ons_X G x = ∑ F ∈ evenSubgraphs G, x ^ F.card := by
-- proof
  apply StatMech.Onsager.ons_X_eq_sum_evenSubgraphs x

/--
[evenSubgraph_walk_decomp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CoeffMatch.lean)
-/
@[path]
private lemma evenSubgraph_walk_decomp_eq
  {V : Type}
  [Fintype V]
  [DecidableEq V]
  {F : Finset (Sym2 V)}
-- given
  (hF : F ∈ evenSubgraphs G) :
-- imply
  ∃ (ι : Type) (_ : DecidableEq ι) (s : Finset ι) (w : ι → V) (W : (i : ι) → G.Walk (w i) (w i)), F = s.biUnion (fun i => (W i).edges.toFinset) ∧ (s : Set ι).PairwiseDisjoint (fun i => (W i).edges.toFinset) := by
-- proof
  apply StatMech.Onsager.evenSubgraph_walk_decomp F hF

/--
[evenSubgraph_weight_factor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CoeffMatch.lean)
-/
@[path]
private lemma evenSubgraph_weight_factor_eq
  {V : Type}
  [Fintype V]
  [DecidableEq V]
  {x : ℝ}
  {F : Finset (Sym2 V)}
-- given
  (hF : F ∈ evenSubgraphs G) :
-- imply
  ∃ (ι : Type) (_ : DecidableEq ι) (s : Finset ι) (w : ι → V) (W : (i : ι) → G.Walk (w i) (w i)), F = s.biUnion (fun i => (W i).edges.toFinset) ∧ (s : Set ι).PairwiseDisjoint (fun i => (W i).edges.toFinset) ∧ x ^ F.card = ∏ i ∈ s, x ^ (W i).edges.toFinset.card := by
-- proof
  apply StatMech.Onsager.evenSubgraph_weight_factor x F hF

/--
[ons_X_eq_sum_prod_over_loops](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CoeffMatch.lean)
-/
@[path]
private lemma ons_X_eq_sum_prod_over_loops_eq
  {V : Type}
  [Fintype V]
  [DecidableEq V]
  {x : ℝ} :
-- imply
  ∃ f : Finset (Sym2 V) → ℝ, (∀ F ∈ evenSubgraphs G, ∃ (ι : Type) (_ : DecidableEq ι) (s : Finset ι) (w : ι → V) (W : (i : ι) → G.Walk (w i) (w i)), F = s.biUnion (fun i => (W i).edges.toFinset) ∧ (s : Set ι).PairwiseDisjoint (fun i => (W i).edges.toFinset) ∧ f F = ∏ i ∈ s, x ^ (W i).edges.toFinset.card) ∧ ons_X G x = ∑ F ∈ evenSubgraphs G, f F := by
-- proof
  apply StatMech.Onsager.ons_X_eq_sum_prod_over_loops x

/--
[incCount_le_degree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CoeffMatch.lean)
-/
@[path]
private lemma incCount_le_degree_eq
  {V : Type}
  [Fintype V]
  [DecidableEq V]
  {F : Finset (Sym2 V)}
  {v : V}
-- given
  (hFsub : F ⊆ G.edgeFinset) :
-- imply
  incCount F v ≤ G.degree v := by
-- proof
  apply StatMech.Onsager.incCount_le_degree F hFsub v

/--
[incCount_eq_zero_or_two_of_trivalent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CoeffMatch.lean)
-/
@[path]
private lemma incCount_eq_zero_or_two_of_trivalent_eq
  {V : Type}
  [Fintype V]
  [DecidableEq V]
  {F : Finset (Sym2 V)}
  {v : V}
-- given
  (hdeg : ∀ v, G.degree v ≤ 3)
  (hF : F ∈ evenSubgraphs G) :
-- imply
  incCount F v = 0 ∨ incCount F v = 2 := by
-- proof
  apply StatMech.Onsager.incCount_eq_zero_or_two_of_trivalent hdeg F hF v


-- created on 2026-10-23
