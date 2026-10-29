import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.AnAlgorithmistsToolkit.code.HallTheorem.Part2
open Finset Function SimpleGraph HallTheorem


namespace HallTheorem

/--
[hall_marriage_theorem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/HallTheorem.lean)
-/
@[path]
lemma hall_marriage_theorem
  [Finite L]
  [DecidableEq R]
  {neighbors : L → Finset R} :
-- imply
  (∀ (S : Finset L), S.card ≤ (S.biUnion neighbors).card) ↔ ∃ f : L → R, Function.Injective f ∧ ∀ x, f x ∈ neighbors x :=
-- proof
  Finset.all_card_le_biUnion_card_iff_existsInjective' neighbors

end HallTheorem

namespace HallTheorem

/--
[bipartite_expander_matching](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/HallTheorem.lean)
-/
@[path]
lemma bipartite_expander_matching
  [DecidableEq L]
  [DecidableEq R]
  [Fintype L]
  {neighbors : L → Finset R}
  {α β : ℝ}
  {S : Finset L}
-- given
  (hexp : BipartiteExpander neighbors α β)
  (hβ : 1 < β)
  (hS : (S.card : ℝ) ≤ α * (Fintype.card L : ℝ)) :
-- imply
  ∃ f : S → R, Function.Injective f ∧ ∀ x : S, f x ∈ neighbors x := by
-- proof
  classical
  rw [← Finset.all_card_le_biUnion_card_iff_existsInjective']
  intro S'
  let S'L : Finset L := S'.image (Subtype.val)
  have hS'L_card : S'L.card = S'.card :=
    Finset.card_image_of_injective S' Subtype.coe_injective
  have hS'L_sub : S'L ⊆ S := by
    intro x hx
    simp only [S'L, Finset.mem_image] at hx
    obtain ⟨⟨y, hy⟩, _, rfl⟩ := hx
    exact hy
  have hS'L_small : (S'L.card : ℝ) ≤ α * (Fintype.card L : ℝ) :=
    calc (S'L.card : ℝ) ≤ (S.card : ℝ) := by exact_mod_cast Finset.card_le_card hS'L_sub
      _ ≤ α * (Fintype.card L : ℝ) := hS
  have hexp_S'L := hexp S'L hS'L_small
  have h_biUnion_eq : S'L.biUnion neighbors = S'.biUnion (fun x => neighbors x) := by
    ext r
    simp only [S'L, Finset.mem_biUnion, Finset.mem_image]
    constructor
    · rintro ⟨l, ⟨⟨s, hs, rfl⟩, hr⟩⟩
      exact ⟨s, hs, hr⟩
    · rintro ⟨⟨l, hl⟩, hs, hr⟩
      exact ⟨l, ⟨⟨⟨l, hl⟩, hs, rfl⟩, hr⟩⟩
  rw [← h_biUnion_eq, ← hS'L_card]
  by_cases hS'_empty : S'L.card = 0
  · simp [hS'_empty]
  ·
    have hS'_pos : (0 : ℝ) < S'L.card := by exact_mod_cast Nat.pos_of_ne_zero hS'_empty
    have : (S'L.card : ℝ) < ((S'L.biUnion neighbors).card : ℝ) :=
      calc (S'L.card : ℝ) = 1 * S'L.card := by ring
        _ < β * S'L.card := by nlinarith
        _ ≤ (S'L.biUnion neighbors).card := hexp_S'L
    exact_mod_cast le_of_lt this

end HallTheorem

namespace HallTheorem

/--
[multibutterfly_can_route](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/HallTheorem.lean)
-/
@[path]
lemma multibutterfly_can_route
  {N numLayers : ℕ}
  {net : MultibutterflyNetwork N numLayers}
  {assignments : RoutingAssignment N numLayers net.α} :
-- imply
  ∀ (i : Fin numLayers), (∃ fUp : (assignments i).up → Fin N, Function.Injective fUp ∧ ∀ x : (assignments i).up, fUp x ∈ net.upNeighbors i (x : Fin N)) ∧ (∃ fDown : (assignments i).down → Fin N, Function.Injective fDown ∧ ∀ x : (assignments i).down, fDown x ∈ net.downNeighbors i (x : Fin N)) := by
-- proof
  intro i
  refine ⟨?_, ?_⟩
  ·
    exact bipartite_expander_matching (net.upNeighbors i) net.α net.β
      (net.upIsExpander i) net.hβ (assignments i).up
      (by simp only [Fintype.card_fin]; exact (assignments i).up_small)
  ·
    exact bipartite_expander_matching (net.downNeighbors i) net.α net.β
      (net.downIsExpander i) net.hβ (assignments i).down
      (by simp only [Fintype.card_fin]; exact (assignments i).down_small)

end HallTheorem

namespace HallTheorem

/--
[unique_neighbors_lower_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/HallTheorem.lean)
-/
@[path]
lemma unique_neighbors_lower_bound
  [DecidableEq R]
  {neighbors : L → Finset R}
  {d : ℕ}
  {β : ℝ}
  {S : Finset L}
  {A B : Finset R}
-- given
  (hexp : (β * S.card : ℝ) ≤ ((S.biUnion neighbors).card : ℝ))
  (hAB_union : A ∪ B = S.biUnion neighbors)
  (hAB_disj : Disjoint A B)
  (hedge : (A.card : ℝ) + 2 * (B.card : ℝ) ≤ (d : ℝ) * S.card) :
-- imply
  ((2 * β - d) * S.card : ℝ) ≤ (A.card : ℝ) := by
-- proof
  have hAB_card : (A.card : ℝ) + (B.card : ℝ) ≥ β * S.card := by
    have h1 : (A ∪ B).card = A.card + B.card := Finset.card_union_of_disjoint hAB_disj
    have h2 : ((S.biUnion neighbors).card : ℝ) = (A.card : ℝ) + (B.card : ℝ) := by
      rw [← hAB_union]; exact_mod_cast h1
    linarith
  linarith
end HallTheorem
namespace SimpleGraph
section HallMatchingLemma
open Finset


namespace SimpleGraph

/--
[bipartiteNeighborFinset_eq_filter_pos](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/HallTheorem.lean)
-/
@[path]
lemma bipartiteNeighborFinset_eq_filter_pos
  [Fintype L]
  [Fintype R]
  [DecidableEq L]
  [DecidableEq R]
  {G : SimpleGraph (L ⊕ R)}
  [DecidableRel G.Adj]
  {S : Finset L} :
-- imply
  G.bipartiteNeighborFinset S = Finset.univ.filter fun r => 0 < G.rightDegreeInS S r := by
-- proof
  ext r
  simp only [bipartiteNeighborFinset, Finset.mem_filter, Finset.mem_univ, true_and,
    rightDegreeInS]
  constructor
  · rintro ⟨l, hl, hadj⟩
    exact Finset.card_pos.mpr ⟨l, Finset.mem_filter.mpr ⟨hl, hadj⟩⟩
  · intro h
    obtain ⟨l, hl⟩ := Finset.card_pos.mp h
    rw [Finset.mem_filter] at hl
    exact ⟨l, hl.1, hl.2⟩

end SimpleGraph

namespace SimpleGraph

/--
[bipartiteNeighborFinset_eq_unique_union_multi](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/HallTheorem.lean)
-/
@[path]
lemma bipartiteNeighborFinset_eq_unique_union_multi
  [Fintype L]
  [Fintype R]
  [DecidableEq L]
  [DecidableEq R]
  {G : SimpleGraph (L ⊕ R)}
  [DecidableRel G.Adj]
  {S : Finset L} :
-- imply
  G.bipartiteNeighborFinset S = G.uniqueNeighbors S ∪ G.multiNeighbors S := by
-- proof
  rw [G.bipartiteNeighborFinset_eq_filter_pos S]
  ext r
  simp only [uniqueNeighbors, multiNeighbors, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_union]
  omega

end SimpleGraph

namespace SimpleGraph

/--
[uniqueNeighbors_disjoint_multiNeighbors](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/HallTheorem.lean)
-/
@[path]
lemma uniqueNeighbors_disjoint_multiNeighbors
  [Fintype L]
  [Fintype R]
  [DecidableEq L]
  [DecidableEq R]
  {G : SimpleGraph (L ⊕ R)}
  [DecidableRel G.Adj]
  {S : Finset L} :
-- imply
  Disjoint (G.uniqueNeighbors S) (G.multiNeighbors S) := by
-- proof
  simp only [uniqueNeighbors, multiNeighbors]
  rw [Finset.disjoint_filter]
  intro _ _ h1 h2; omega

end SimpleGraph

namespace SimpleGraph

/--
[card_filter_adj_right_eq_of_regular_bipartite](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/HallTheorem.lean)
-/
@[path]
lemma card_filter_adj_right_eq_of_regular_bipartite
  [Fintype L]
  [Fintype R]
  [DecidableEq L]
  [DecidableEq R]
  {G : SimpleGraph (L ⊕ R)}
  [DecidableRel G.Adj]
  {d : ℕ}
  {l : L}
-- given
  (hbip : G.IsBipartiteOn)
  (hreg : G.IsRegularOfDegree d) :
-- imply
  (Finset.univ.filter fun r => G.Adj (Sum.inl l) (Sum.inr r)).card = d := by
-- proof
  have hdeg := hreg (Sum.inl l)
  suffices G.neighborFinset (Sum.inl l) =
    (Finset.univ.filter fun r => G.Adj (Sum.inl l) (Sum.inr r)).map
      ⟨Sum.inr, Sum.inr_injective⟩ by
    rwa [degree, this, Finset.card_map] at hdeg
  ext x
  simp only [SimpleGraph.mem_neighborFinset, Finset.mem_map, Finset.mem_filter,
    Finset.mem_univ, true_and, Function.Embedding.coeFn_mk]
  constructor
  · intro hadj
    cases x with
    | inl l' => exact absurd hadj (hbip.1 l l')
    | inr r => exact ⟨r, hadj, rfl⟩
  · rintro ⟨r, hadj, rfl⟩
    exact hadj

end SimpleGraph

namespace SimpleGraph

/--
[sum_leftRightDegree_eq_d_mul_card](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/HallTheorem.lean)
-/
@[path]
lemma sum_leftRightDegree_eq_d_mul_card
  [Fintype L]
  [Fintype R]
  [DecidableEq L]
  [DecidableEq R]
  {G : SimpleGraph (L ⊕ R)}
  [DecidableRel G.Adj]
  {d : ℕ}
  {S : Finset L}
-- given
  (hbip : G.IsBipartiteOn)
  (hreg : G.IsRegularOfDegree d) :
-- imply
  (S.sum fun l => (Finset.univ.filter fun r => G.Adj (Sum.inl l) (Sum.inr r)).card) = d * S.card := by
-- proof
  simp only [G.card_filter_adj_right_eq_of_regular_bipartite hbip hreg]
  simp [Finset.sum_const, mul_comm]

end SimpleGraph

namespace SimpleGraph

/--
[double_count_edges](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/HallTheorem.lean)
-/
@[path]
lemma double_count_edges
  [Fintype L]
  [Fintype R]
  [DecidableEq L]
  [DecidableEq R]
  {G : SimpleGraph (L ⊕ R)}
  [DecidableRel G.Adj]
  {S : Finset L} :
-- imply
  (S.sum fun l => (Finset.univ.filter fun r => G.Adj (Sum.inl l) (Sum.inr r)).card) = (Finset.univ.sum fun r => G.rightDegreeInS S r) := by
-- proof
  simp only [rightDegreeInS, Finset.card_filter]
  rw [Finset.sum_comm]

end SimpleGraph

namespace SimpleGraph

/--
[sum_rightDegreeInS_ge](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/HallTheorem.lean)
-/
@[path]
lemma sum_rightDegreeInS_ge
  [Fintype L]
  [Fintype R]
  [DecidableEq L]
  [DecidableEq R]
  {G : SimpleGraph (L ⊕ R)}
  [DecidableRel G.Adj]
  {S : Finset L} :
-- imply
  (Finset.univ.sum fun r => G.rightDegreeInS S r) ≥ (G.uniqueNeighbors S).card + 2 * (G.multiNeighbors S).card := by
-- proof
  have hd := G.uniqueNeighbors_disjoint_multiNeighbors S
  have hunion : Finset.univ.sum (fun r => G.rightDegreeInS S r) ≥
    (G.uniqueNeighbors S ∪ G.multiNeighbors S).sum (fun r => G.rightDegreeInS S r) :=
    Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  have hsplit : (G.uniqueNeighbors S ∪ G.multiNeighbors S).sum (fun r => G.rightDegreeInS S r) =
    (G.uniqueNeighbors S).sum (fun r => G.rightDegreeInS S r) +
    (G.multiNeighbors S).sum (fun r => G.rightDegreeInS S r) :=
    Finset.sum_union hd
  have hunique : (G.uniqueNeighbors S).sum (fun r => G.rightDegreeInS S r) =
    (G.uniqueNeighbors S).card := by
    rw [Finset.card_eq_sum_ones]
    apply Finset.sum_congr rfl
    intro r hr
    simp only [uniqueNeighbors, Finset.mem_filter] at hr
    exact hr.2
  have hmulti : (G.multiNeighbors S).sum (fun r => G.rightDegreeInS S r) ≥
    2 * (G.multiNeighbors S).card := by
    rw [Finset.card_eq_sum_ones, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro r hr
    simp only [multiNeighbors, Finset.mem_filter] at hr
    linarith [hr.2]
  linarith

end SimpleGraph

namespace SimpleGraph

/--
[unique_neighbors_lower_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/HallTheorem.lean)
-/
@[path]
lemma unique_neighbors_lower_bound
  [Fintype L]
  [Fintype R]
  [DecidableEq L]
  [DecidableEq R]
  {G : SimpleGraph (L ⊕ R)}
  [DecidableRel G.Adj]
  {d : ℕ}
  {α β : ℝ}
  {S : Finset L}
-- given
  (hbip : G.IsBipartiteOn)
  (hreg : G.IsRegularOfDegree d)
  (hexp : G.IsBipartiteExpander α β)
  (hS : (S.card : ℝ) ≤ α * (Fintype.card L : ℝ)) :
-- imply
  ((G.uniqueNeighbors S).card : ℝ) ≥ (2 * β - ↑d) * (S.card : ℝ) := by
-- proof
  set A := G.uniqueNeighbors S with hA_def
  set B := G.multiNeighbors S with hB_def
  have hexp_ineq : (A.card : ℝ) + (B.card : ℝ) ≥ β * (S.card : ℝ) := by
    have hNS := hexp S hS
    rw [G.bipartiteNeighborFinset_eq_unique_union_multi S,
      Finset.card_union_of_disjoint (G.uniqueNeighbors_disjoint_multiNeighbors S)] at hNS
    push_cast at hNS ⊢
    linarith
  have hedge : (d : ℝ) * (S.card : ℝ) ≥ (A.card : ℝ) + 2 * (B.card : ℝ) := by
    have h1 := G.sum_rightDegreeInS_ge S
    rw [← G.double_count_edges S,
      G.sum_leftRightDegree_eq_d_mul_card hbip hreg S] at h1
    exact_mod_cast h1
  nlinarith
end HallMatchingLemma

end SimpleGraph


-- created on 2026-10-23
-- updated on 2026-10-28
