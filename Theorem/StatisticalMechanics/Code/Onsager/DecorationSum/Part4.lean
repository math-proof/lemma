/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationSum.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.SpinCharacter.Part2
import Theorem.StatisticalMechanics.Code.Onsager.TorusDecoration.Part13
import Def.StatisticalMechanics.Code.Onsager.DecorationSum.Part4


namespace StatMech.Onsager

open BigOperators StatMech.Ising

theorem ons_walkOriginalEdges_even {L : ℕ} [Fact (2 < L)]
    {v : ons_Dart L} (p : (ons_decGraph L).Walk v v)
    (hp : p.IsCycle) :
    ons_walkOriginalEdges p ∈ evenSubgraphs (onsTorusGraph L) := by
  let D : ons_DecoratedEvenSubgraph L :=
    ⟨p.edges.toFinset,
      ons_cycle_edges_evenSubgraph (ons_decGraph L) p hp⟩
  have h := ons_originalEdgesOfDecorated_even L D
  rw [← ons_decoratedExternalEdges_image L D] at h
  simpa only [ons_walkOriginalEdges, ons_walkExternalEdges, D] using h

theorem ons_decoratedExternalEdges_card_biUnion
    {L : ℕ} [Fact (2 < L)]
    {iota : Type} [Fintype iota] [DecidableEq iota]
    (D : Finset (Sym2 (ons_Dart L)))
    (piece : iota → Finset (Sym2 (ons_Dart L)))
    (hcover : D = Finset.univ.biUnion piece)
    (hdisj : ((Finset.univ : Finset iota) : Set iota).PairwiseDisjoint piece) :
    (ons_decoratedExternalEdges D).card =
      ∑ i, (ons_decoratedExternalEdges (piece i)).card := by
  classical
  have hcoverExt : ons_decoratedExternalEdges D =
      Finset.univ.biUnion (fun i => ons_decoratedExternalEdges (piece i)) := by
    ext edge
    simp only [ons_decoratedExternalEdges, Finset.mem_filter,
      Finset.mem_biUnion, Finset.mem_univ, true_and]
    rw [hcover]
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
    aesop
  rw [hcoverExt]
  exact Finset.card_biUnion (fun i hi j hj hij =>
    (hdisj (Finset.mem_coe.mpr hi) (Finset.mem_coe.mpr hj) hij).mono
      (Finset.filter_subset _ _) (Finset.filter_subset _ _))

theorem ons_decoratedExternal_pow_factor
    {L : ℕ} [Fact (2 < L)]
    {iota : Type} [Fintype iota] [DecidableEq iota]
    (x : ℝ) (D : Finset (Sym2 (ons_Dart L)))
    (piece : iota → Finset (Sym2 (ons_Dart L)))
    (hcover : D = Finset.univ.biUnion piece)
    (hdisj : ((Finset.univ : Finset iota) : Set iota).PairwiseDisjoint piece) :
    x ^ (ons_decoratedExternalEdges D).card =
      ∏ i, x ^ (ons_decoratedExternalEdges (piece i)).card := by
  rw [ons_decoratedExternalEdges_card_biUnion D piece hcover hdisj,
    Finset.prod_pow_eq_pow_sum]

theorem ons_originalHomology_biUnion
    {L : ℕ} [Fact (2 < L)]
    {iota : Type} [Fintype iota] [DecidableEq iota]
    (D : ons_DecoratedEvenSubgraph L)
    (piece : iota → Finset (Sym2 (ons_Dart L)))
    (hcover : D.1 = Finset.univ.biUnion piece)
    (hdisj : ((Finset.univ : Finset iota) : Set iota).PairwiseDisjoint piece) :
    ons_evenHomology L (ons_originalEdgesOfDecorated L D) =
      ∑ i, ons_evenHomology L
        ((ons_decoratedExternalEdges (piece i)).image ons_decEdgeProjection) := by
  classical
  have hcoverExt : ons_decoratedExternalEdges D.1 =
      Finset.univ.biUnion (fun i => ons_decoratedExternalEdges (piece i)) := by
    ext edge
    simp only [ons_decoratedExternalEdges, Finset.mem_filter,
      Finset.mem_biUnion, Finset.mem_univ, true_and]
    rw [hcover]
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
    aesop
  have hdisjProj : ((Finset.univ : Finset iota) : Set iota).PairwiseDisjoint
      (fun i => (ons_decoratedExternalEdges (piece i)).image
        ons_decEdgeProjection) := by
    intro i hi j hj hij
    change Disjoint
      ((ons_decoratedExternalEdges (piece i)).image ons_decEdgeProjection)
      ((ons_decoratedExternalEdges (piece j)).image ons_decEdgeProjection)
    rw [Finset.disjoint_left]
    intro edge hei hej
    rcases Finset.mem_image.mp hei with ⟨di, hdi, rfl⟩
    rcases Finset.mem_image.mp hej with ⟨dj, hdj, hproj⟩
    have hdiData := Finset.mem_filter.mp hdi
    have hdjData := Finset.mem_filter.mp hdj
    have hdart : di = dj :=
      ons_decEdgeProjection_injective_of_external L
        hdiData.2 hdjData.2 hproj.symm
    subst dj
    exact (Finset.disjoint_left.mp (hdisj hi hj hij)) hdiData.1 hdjData.1
  calc
    ons_evenHomology L (ons_originalEdgesOfDecorated L D) =
        ons_evenHomology L
          ((ons_decoratedExternalEdges D.1).image ons_decEdgeProjection) := by
      rw [ons_decoratedExternalEdges_image]
    _ = ons_evenHomology L
        (Finset.univ.biUnion (fun i =>
          (ons_decoratedExternalEdges (piece i)).image ons_decEdgeProjection)) := by
      rw [hcoverExt, Finset.biUnion_image]
    _ = ∑ i, ons_evenHomology L
        ((ons_decoratedExternalEdges (piece i)).image ons_decEdgeProjection) :=
      ons_evenHomology_biUnion Finset.univ _ hdisjProj

theorem ons_decoratedSpinWeight_factor_of_isotropic
    {L : ℕ} [Fact (2 < L)]
    {iota : Type} [Fintype iota] [DecidableEq iota]
    (x : ℝ) (a b : Fin 2) (D : ons_DecoratedEvenSubgraph L)
    (piece : iota → Finset (Sym2 (ons_Dart L)))
    (hcover : D.1 = Finset.univ.biUnion piece)
    (hdisj : ((Finset.univ : Finset iota) : Set iota).PairwiseDisjoint piece)
    (hisotropic : ∀ i j, i ≠ j →
      ons_homologyIntersection
        (ons_evenHomology L
          ((ons_decoratedExternalEdges (piece i)).image ons_decEdgeProjection))
        (ons_evenHomology L
          ((ons_decoratedExternalEdges (piece j)).image ons_decEdgeProjection)) = 0) :
    ons_decoratedSpinWeight L x a b D =
      ∏ i,
        ons_spinCharacter a b
            (ons_evenHomology L
              ((ons_decoratedExternalEdges (piece i)).image
                ons_decEdgeProjection)) *
          x ^ (ons_decoratedExternalEdges (piece i)).card := by
  let h : iota → Fin 2 × Fin 2 := fun i =>
    ons_evenHomology L
      ((ons_decoratedExternalEdges (piece i)).image ons_decEdgeProjection)
  have hchar : ons_spinCharacter a b
      (ons_evenHomology L (ons_originalEdgesOfDecorated L D)) =
      ∏ i, ons_spinCharacter a b (h i) := by
    rw [ons_originalHomology_biUnion D piece hcover hdisj]
    exact ons_spinCharacter_sum_of_pairwise_intersection_zero
      a b Finset.univ h (by
        intro i _ j _ hij
        exact hisotropic i j hij)
  have hpow := ons_decoratedExternal_pow_factor x D.1 piece hcover hdisj
  rw [ons_decoratedSpinWeight_eq_external, hchar, hpow,
    Finset.prod_mul_distrib]

theorem sum_finset_eq_sum_subtype
    {alpha R : Type*} [Fintype alpha] [DecidableEq alpha]
    [AddCommMonoid R] (S : Finset alpha) (f : alpha → R) :
    ∑ x ∈ S, f x = ∑ x : {x // x ∈ S}, f x.1 := by
  exact Finset.sum_subtype S (fun _ => Iff.rfl) f


theorem ons_spinCharacterSum_eq_decorated
    (L : ℕ) [Fact (2 < L)] (x : ℝ) (a b : Fin 2) :
    ons_spinCharacterSum L x a b =
      ∑ D : ons_DecoratedEvenSubgraph L,
        ons_decoratedSpinWeight L x a b D := by
  unfold ons_spinCharacterSum
  rw [sum_finset_eq_sum_subtype]
  have hsum := Equiv.sum_comp (ons_decorationEquiv L)
    (fun D : ons_DecoratedEvenSubgraph L =>
      ons_decoratedSpinWeight L x a b D)
  simpa [ons_decoratedSpinWeight, ons_originalEdgesOfDecorated] using hsum


theorem ons_decoratedSpinTerm_cycle_decomposition
    (L : ℕ) [Fact (2 < L)]
    (D : ons_DecoratedEvenSubgraph L) :
    ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι)
      (base : ι → ons_Dart L)
      (p : (i : ι) → (ons_decGraph L).Walk (base i) (base i)),
      (∀ i, (p i).IsCycle) ∧
      D.1 = Finset.univ.biUnion (fun i => (p i).edges.toFinset) ∧
      ((Finset.univ : Finset ι) : Set ι).PairwiseDisjoint
        (fun i => (p i).edges.toFinset) ∧
      ((Finset.univ : Finset ι) : Set ι).PairwiseDisjoint
        (fun i => (p i).toSubgraph.verts) := by
  exact ons_trivalent_even_cycle_decomposition
    (ons_decGraph L) (ons_decGraph_degree_le_three L) D.1 D.2


theorem ons_decoratedSpinTerm_cycle_weight_factor
    (L : ℕ) [Fact (2 < L)] (x : ℝ)
    (D : ons_DecoratedEvenSubgraph L) :
    ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι)
      (base : ι → ons_Dart L)
      (p : (i : ι) → (ons_decGraph L).Walk (base i) (base i)),
      (∀ i, (p i).IsCycle) ∧
      D.1 = Finset.univ.biUnion (fun i => (p i).edges.toFinset) ∧
      ((Finset.univ : Finset ι) : Set ι).PairwiseDisjoint
        (fun i => (p i).edges.toFinset) ∧
      ((Finset.univ : Finset ι) : Set ι).PairwiseDisjoint
        (fun i => (p i).toSubgraph.verts) ∧
      x ^ (ons_originalEdgesOfDecorated L D).card =
        ∏ i, x ^ (ons_walkExternalEdges (p i)).card := by
  obtain ⟨ι, hi, hdeci, base, p, hcycle, hcover, hdisj, hverts⟩ :=
    ons_decoratedSpinTerm_cycle_decomposition L D
  refine ⟨ι, hi, hdeci, base, p, hcycle, hcover, hdisj, hverts, ?_⟩
  rw [ons_originalEdgesOfDecorated_card]
  exact ons_decoratedExternal_pow_factor x D.1
    (fun i => (p i).edges.toFinset) hcover hdisj


theorem ons_decoratedSpinTerm_cycle_data
    (L : ℕ) [Fact (2 < L)] (x : ℝ)
    (D : ons_DecoratedEvenSubgraph L) :
    ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι)
      (base : ι → ons_Dart L)
      (p : (i : ι) → (ons_decGraph L).Walk (base i) (base i)),
      (∀ i, (p i).IsCycle) ∧
      D.1 = Finset.univ.biUnion (fun i => (p i).edges.toFinset) ∧
      ((Finset.univ : Finset ι) : Set ι).PairwiseDisjoint
        (fun i => (p i).edges.toFinset) ∧
      ((Finset.univ : Finset ι) : Set ι).PairwiseDisjoint
        (fun i => (p i).toSubgraph.verts) ∧
      x ^ (ons_originalEdgesOfDecorated L D).card =
        ∏ i, x ^ (ons_walkExternalEdges (p i)).card ∧
      ons_evenHomology L (ons_originalEdgesOfDecorated L D) =
        ∑ i, ons_evenHomology L (ons_walkOriginalEdges (p i)) := by
  obtain ⟨ι, hi, hdeci, base, p, hcycle, hcover, hdisj, hverts⟩ :=
    ons_decoratedSpinTerm_cycle_decomposition L D
  refine ⟨ι, hi, hdeci, base, p, hcycle, hcover, hdisj, hverts, ?_, ?_⟩
  · rw [ons_originalEdgesOfDecorated_card]
    exact ons_decoratedExternal_pow_factor x D.1
      (fun i => (p i).edges.toFinset) hcover hdisj
  · simpa only [ons_walkOriginalEdges, ons_walkExternalEdges] using
      ons_originalHomology_biUnion D
        (fun i => (p i).edges.toFinset) hcover hdisj

end StatMech.Onsager
