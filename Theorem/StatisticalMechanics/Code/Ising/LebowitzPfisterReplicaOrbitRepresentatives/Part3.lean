/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRepresentatives.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitCardinality.Part2
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRepresentatives.Part3
open Finset


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

@[simp] theorem mem_lpReplicaCurrentEdgeOrbitStrictReps
    (G : SimpleGraph V) (sites : I -> V)
    (e : (lpReplicaCurrentGraph G sites).edgeFinset) :
    e ∈ lpReplicaCurrentEdgeOrbitStrictReps G sites ↔
      e ∈ lpReplicaCurrentEdgeOrbitReps G sites ∧
        e ≠ lpReplicaCurrentEdgeReflect G sites e := by
  classical
  simp [lpReplicaCurrentEdgeOrbitStrictReps]

@[simp] theorem mem_lpReplicaCurrentEdgeOrbitFixed
    (G : SimpleGraph V) (sites : I -> V)
    (e : (lpReplicaCurrentGraph G sites).edgeFinset) :
    e ∈ lpReplicaCurrentEdgeOrbitFixed G sites ↔
      e = lpReplicaCurrentEdgeReflect G sites e := by
  classical
  simp [lpReplicaCurrentEdgeOrbitFixed]


theorem lpReplicaCurrentEdge_reflect_strictReps_eq_compl_reps
    (G : SimpleGraph V) (sites : I -> V) :
    (lpReplicaCurrentEdgeOrbitStrictReps G sites).map
        (lpReplicaCurrentEdgeReflect G sites).toEmbedding =
      Finset.univ \ lpReplicaCurrentEdgeOrbitReps G sites := by
  classical
  ext e
  constructor
  · intro he
    obtain ⟨x, hx, hxe⟩ := Finset.mem_map.mp he
    rw [mem_lpReplicaCurrentEdgeOrbitStrictReps] at hx
    rw [Finset.mem_sdiff]
    refine ⟨Finset.mem_univ _, ?_⟩
    subst e
    exact (lpReplicaCurrentEdge_mem_reps_iff_reflect_not_mem_reps_of_ne
      G sites x hx.2).mp hx.1
  · intro he
    rw [Finset.mem_sdiff] at he
    let x := lpReplicaCurrentEdgeReflect G sites e
    have hne : e ≠ lpReplicaCurrentEdgeReflect G sites e := by
      intro hfixed
      apply he.2
      rw [mem_lpReplicaCurrentEdgeOrbitReps]
      exact le_of_eq (congrArg (lpReplicaCurrentEdgeRank G sites) hfixed)
    have hxne : x ≠ lpReplicaCurrentEdgeReflect G sites x := by
      intro hx
      apply hne
      change lpReplicaCurrentEdgeReflect G sites e =
        lpReplicaCurrentEdgeReflect G sites
          (lpReplicaCurrentEdgeReflect G sites e) at hx
      exact (lpReplicaCurrentEdgeReflect G sites).injective hx
    have hxrep : x ∈ lpReplicaCurrentEdgeOrbitReps G sites := by
      rcases lpReplicaCurrentEdge_mem_reps_or_reflect_mem_reps
          G sites e with here | href
      · exact False.elim (he.2 here)
      · exact href
    apply Finset.mem_map.mpr
    refine ⟨x, (mem_lpReplicaCurrentEdgeOrbitStrictReps
      G sites x).2 ⟨hxrep, hxne⟩, ?_⟩
    exact lpReplicaCurrentEdgeReflect_involutive G sites e


theorem lpReplicaCurrentEdge_univ_eq_fixed_union_reps_union_reflect
    (G : SimpleGraph V) (sites : I -> V) :
    (Finset.univ : Finset
        (lpReplicaCurrentGraph G sites).edgeFinset) =
      lpReplicaCurrentEdgeOrbitFixed G sites ∪
        (lpReplicaCurrentEdgeOrbitStrictReps G sites ∪
          (lpReplicaCurrentEdgeOrbitStrictReps G sites).map
            (lpReplicaCurrentEdgeReflect G sites).toEmbedding) := by
  classical
  ext e
  simp only [Finset.mem_univ, true_iff, Finset.mem_union,
    mem_lpReplicaCurrentEdgeOrbitFixed,
    mem_lpReplicaCurrentEdgeOrbitStrictReps,
    lpReplicaCurrentEdge_reflect_strictReps_eq_compl_reps,
    Finset.mem_sdiff]
  by_cases hfixed : e = lpReplicaCurrentEdgeReflect G sites e
  · exact Or.inl hfixed
  · right
    by_cases hrep : e ∈ lpReplicaCurrentEdgeOrbitReps G sites
    · exact Or.inl ⟨hrep, hfixed⟩
    · exact Or.inr ⟨True.intro, hrep⟩

theorem lpReplicaCurrentEdge_fixed_subset_reps
    (G : SimpleGraph V) (sites : I -> V) :
    lpReplicaCurrentEdgeOrbitFixed G sites ⊆
      lpReplicaCurrentEdgeOrbitReps G sites := by
  intro e he
  rw [mem_lpReplicaCurrentEdgeOrbitFixed] at he
  rw [mem_lpReplicaCurrentEdgeOrbitReps]
  exact le_of_eq (congrArg (lpReplicaCurrentEdgeRank G sites) he)

theorem lpReplicaCurrentEdge_strictReps_subset_reps
    (G : SimpleGraph V) (sites : I -> V) :
    lpReplicaCurrentEdgeOrbitStrictReps G sites ⊆
      lpReplicaCurrentEdgeOrbitReps G sites := by
  intro e he
  exact (mem_lpReplicaCurrentEdgeOrbitStrictReps G sites e).1 he |>.1

theorem lpReplicaCurrentEdge_disjoint_reps_reflectStrictReps
    (G : SimpleGraph V) (sites : I -> V) :
    Disjoint (lpReplicaCurrentEdgeOrbitReps G sites)
      ((lpReplicaCurrentEdgeOrbitStrictReps G sites).map
        (lpReplicaCurrentEdgeReflect G sites).toEmbedding) := by
  rw [lpReplicaCurrentEdge_reflect_strictReps_eq_compl_reps]
  rw [Finset.disjoint_left]
  intro e he hcomp
  exact (Finset.mem_sdiff.mp hcomp).2 he

theorem lpReplicaCurrentEdge_disjoint_strictReps_reflectStrictReps
    (G : SimpleGraph V) (sites : I -> V) :
    Disjoint (lpReplicaCurrentEdgeOrbitStrictReps G sites)
      ((lpReplicaCurrentEdgeOrbitStrictReps G sites).map
        (lpReplicaCurrentEdgeReflect G sites).toEmbedding) :=
  Finset.disjoint_of_subset_left
    (lpReplicaCurrentEdge_strictReps_subset_reps G sites)
    (lpReplicaCurrentEdge_disjoint_reps_reflectStrictReps G sites)

theorem lpReplicaCurrentEdge_disjoint_fixed_repsUnionReflect
    (G : SimpleGraph V) (sites : I -> V) :
    Disjoint (lpReplicaCurrentEdgeOrbitFixed G sites)
      (lpReplicaCurrentEdgeOrbitStrictReps G sites ∪
        (lpReplicaCurrentEdgeOrbitStrictReps G sites).map
          (lpReplicaCurrentEdgeReflect G sites).toEmbedding) := by
  rw [Finset.disjoint_left]
  intro e hfixed hunion
  rw [Finset.mem_union] at hunion
  rcases hunion with hstrict | hreflect
  · exact (mem_lpReplicaCurrentEdgeOrbitStrictReps G sites e).1
      hstrict |>.2 ((mem_lpReplicaCurrentEdgeOrbitFixed G sites e).1 hfixed)
  · exact (Finset.disjoint_left.mp
      (lpReplicaCurrentEdge_disjoint_reps_reflectStrictReps G sites))
        ((lpReplicaCurrentEdge_fixed_subset_reps G sites) hfixed) hreflect


theorem lpReplicaCurrentEdge_prod_orbitPairs
    (G : SimpleGraph V) (sites : I -> V)
    {M : Type*} [CommMonoid M]
    (f : (lpReplicaCurrentGraph G sites).edgeFinset -> M) :
    (∏ e, f e) =
      (∏ e ∈ lpReplicaCurrentEdgeOrbitFixed G sites, f e) *
        ∏ e ∈ lpReplicaCurrentEdgeOrbitStrictReps G sites,
          (f e * f (lpReplicaCurrentEdgeReflect G sites e)) := by
  classical
  conv_lhs =>
    rw [lpReplicaCurrentEdge_univ_eq_fixed_union_reps_union_reflect
      G sites]
  rw [Finset.prod_union
    (lpReplicaCurrentEdge_disjoint_fixed_repsUnionReflect G sites)]
  rw [Finset.prod_union
    (lpReplicaCurrentEdge_disjoint_strictReps_reflectStrictReps G sites)]
  rw [Finset.prod_map]
  rw [Finset.prod_mul_distrib]
  rfl

end
end StatMech.Ising
