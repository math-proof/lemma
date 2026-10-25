/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Varieties.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.ArithmeticGeometry.code.AffineVarieties.Part5
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.AffineVarieties
import Mathlib.Topology.Basic
import Mathlib.Topology.Order
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Def.v1.Atlas.ArithmeticGeometry.code.Varieties.Part5
variable (k : Type*) [Field k]


/-- The empty set is an algebraic set, namely $\mathcal{V}(\{1\})$. -/
lemma algebraicSetsCollection_empty_mem (n : ℕ) : ∅ ∈ algebraicSetsCollection k n :=
  ⟨{1}, by ext P; simp [AlgebraicSet]⟩

/-- An arbitrary intersection of algebraic sets is again algebraic. -/
lemma algebraicSetsCollection_sInter_mem (n : ℕ) (A : Set (Set (AffineSpace_k k n)))
    (hA : A ⊆ algebraicSetsCollection k n) :
    ⋂₀ A ∈ algebraicSetsCollection k n := by
  choose S hS using fun V (hV : V ∈ A) => hA hV
  refine ⟨⋃ V ∈ A, S V ‹_›, ?_⟩
  ext P
  simp only [Set.mem_sInter, AlgebraicSet, Set.mem_setOf_eq, Set.mem_iUnion]
  constructor
  · intro h f ⟨V, hV, hfS⟩
    have := h V hV; rw [hS V hV] at this; exact this f hfS
  · intro h V hV
    rw [hS V hV]; intro f hfS; exact h f ⟨V, hV, hfS⟩

/-- The union of two algebraic sets is algebraic: $\mathcal{V}(S) \cup \mathcal{V}(T) = \mathcal{V}(ST)$. -/
lemma algebraicSetsCollection_union_mem (n : ℕ)
    (A : Set (AffineSpace_k k n)) (hA : A ∈ algebraicSetsCollection k n)
    (B : Set (AffineSpace_k k n)) (hB : B ∈ algebraicSetsCollection k n) :
    A ∪ B ∈ algebraicSetsCollection k n := by
  obtain ⟨S, rfl⟩ := hA
  obtain ⟨T, rfl⟩ := hB
  refine ⟨{f * g | (f ∈ S) (g ∈ T)}, ?_⟩
  ext P
  simp only [Set.mem_union, AlgebraicSet, Set.mem_setOf_eq]
  constructor
  · rintro (hS | hT)
    · rintro _ ⟨f, hf, g, hg, rfl⟩; simp [hS f hf]
    · rintro _ ⟨f, hf, g, hg, rfl⟩; simp [hT g hg]
  · intro h
    by_contra hc
    push Not at hc
    obtain ⟨⟨f, hf, hfP⟩, ⟨g, hg, hgP⟩⟩ := hc
    have := h (f * g) ⟨f, hf, g, hg, rfl⟩
    rw [map_mul] at this
    exact (mul_eq_zero.mp this).elim hfP hgP

