/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Morphisms.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.ArithmeticGeometry.code.ProjectiveVarieties.Part7
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.ProjectiveVarieties
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.Varieties
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.VarietyAlgebraEquiv
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.Theorem1324
import Def.v1.Atlas.ArithmeticGeometry.code.Varieties.Part9
import Theorem.v1.Atlas.ArithmeticGeometry.code.VarietyAlgebraEquiv.Part2
import Theorem.v1.Atlas.ArithmeticGeometry.code.Theorem1324
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Topology.Basic
import Mathlib.Topology.Order
import Def.v1.Atlas.ArithmeticGeometry.code.Morphisms.Part2


noncomputable section

open MvPolynomial

variable (k : Type*) [Field k]

/-- The empty set is projectively algebraic: it is cut out by the polynomial
$1$, which has no zeros. -/
lemma projAlgSets_empty_mem (n : ℕ) : ∅ ∈ projAlgSetsCollection k n := by
  refine ⟨{⟨1, 0, MvPolynomial.isHomogeneous_one _ _⟩}, ?_⟩
  ext P
  simp only [Set.mem_empty_iff_false, ProjVanishingSet, Set.mem_setOf_eq, false_iff]
  obtain ⟨v, rfl⟩ := P.exists_rep
  simp only [Quotient.liftOn_mk]
  intro h
  exact absurd (h ⟨1, 0, MvPolynomial.isHomogeneous_one _ _⟩ (Set.mem_singleton _)) (by simp)

/-- Arbitrary intersections of projectively algebraic sets are projectively
algebraic: union the underlying homogeneous polynomial families. -/
lemma projAlgSets_sInter_mem (n : ℕ) (A : Set (Set (ProjectiveSpace_k k n)))
    (hA : A ⊆ projAlgSetsCollection k n) :
    ⋂₀ A ∈ projAlgSetsCollection k n := by
  choose S hS using fun V (hV : V ∈ A) => hA hV
  refine ⟨⋃ (V : Set (ProjectiveSpace_k k n)) (_ : V ∈ A), S V ‹_›, ?_⟩
  ext P
  simp only [Set.mem_sInter, ProjVanishingSet, Set.mem_setOf_eq]
  obtain ⟨v, rfl⟩ := P.exists_rep
  simp only [Quotient.liftOn_mk]
  constructor
  · intro h f hf
    obtain ⟨V, hV, hfS⟩ := Set.mem_iUnion₂.mp hf
    have := h V hV
    rw [hS V hV, ProjVanishingSet, Set.mem_setOf_eq, Quotient.liftOn_mk] at this
    exact this f hfS
  · intro h V hV
    rw [hS V hV, ProjVanishingSet, Set.mem_setOf_eq, Quotient.liftOn_mk]
    exact fun f hfS => h f (Set.mem_iUnion₂.mpr ⟨V, hV, hfS⟩)

/-- The union of two projectively algebraic sets is projectively algebraic:
take pairwise products of the defining homogeneous polynomials. -/
lemma projAlgSets_union_mem (n : ℕ)
    (A : Set (ProjectiveSpace_k k n)) (hA : A ∈ projAlgSetsCollection k n)
    (B : Set (ProjectiveSpace_k k n)) (hB : B ∈ projAlgSetsCollection k n) :
    A ∪ B ∈ projAlgSetsCollection k n := by
  obtain ⟨S, rfl⟩ := hA
  obtain ⟨T, rfl⟩ := hB
  let ST : Set (HomogPoly k n) :=
    {fg | ∃ f ∈ S, ∃ g ∈ T,
      fg = ⟨f.poly * g.poly, f.deg + g.deg, f.isHomog.mul g.isHomog⟩}
  refine ⟨ST, ?_⟩
  ext P
  simp only [Set.mem_union, ProjVanishingSet, Set.mem_setOf_eq]
  obtain ⟨v, rfl⟩ := P.exists_rep
  simp only [Quotient.liftOn_mk]
  constructor
  · rintro (hS | hT) fg ⟨f, hf, g, hg, rfl⟩
    · simp [map_mul, hS f hf]
    · simp [map_mul, hT g hg]
  · intro h
    by_contra hc
    push Not at hc
    obtain ⟨⟨f, hf, hfP⟩, ⟨g, hg, hgP⟩⟩ := hc
    have hmem : (⟨f.poly * g.poly, f.deg + g.deg,
        f.isHomog.mul g.isHomog⟩ : HomogPoly k n) ∈ ST :=
      ⟨f, hf, g, hg, rfl⟩
    have := h _ hmem
    simp only at this
    rw [map_mul] at this
    exact (mul_eq_zero.mp this).elim hfP hgP

end
