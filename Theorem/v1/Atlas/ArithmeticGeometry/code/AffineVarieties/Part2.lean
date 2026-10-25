/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/AffineVarieties.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.FieldTheory.Perfect
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Nullstellensatz
import Def.v1.Atlas.ArithmeticGeometry.code.AffineVarieties.Part3
variable (k : Type*) [Field k]


/-- Membership in $I(Z)$ unfolds to vanishing of $f$ at every point of $Z$. -/
@[simp]
theorem mem_idealOfAlgebraicSet_iff {Z : Set (σ → k)} {f : MvPolynomial σ k} :
    f ∈ idealOfAlgebraicSet Z ↔ ∀ P ∈ Z, MvPolynomial.eval P f = 0 :=
  Iff.rfl

/-- The textbook vanishing ideal `idealOfAlgebraicSet` matches Mathlib's
`MvPolynomial.vanishingIdeal`. -/
theorem idealOfAlgebraicSet_eq_vanishingIdeal (Z : Set (σ → k)) :
    idealOfAlgebraicSet Z = MvPolynomial.vanishingIdeal k Z := by
  ext f
  simp [mem_idealOfAlgebraicSet_iff, MvPolynomial.mem_vanishingIdeal_iff,
    MvPolynomial.aeval_eq_eval]

/-- Antitone: $Y \subseteq Z$ implies $I(Z) \subseteq I(Y)$. -/
theorem idealOfAlgebraicSet_anti_mono {Y Z : Set (σ → k)} (h : Y ⊆ Z) :
    idealOfAlgebraicSet Z ≤ idealOfAlgebraicSet Y :=
  fun _ hf P hP => hf P (h hP)

/-- $I(Y \cup Z) = I(Y) \cap I(Z)$. -/
theorem idealOfAlgebraicSet_union (Y Z : Set (σ → k)) :
    idealOfAlgebraicSet (Y ∪ Z) = idealOfAlgebraicSet Y ⊓ idealOfAlgebraicSet Z := by
  ext f
  simp only [mem_idealOfAlgebraicSet_iff, Ideal.mem_inf, Set.mem_union]
  constructor
  · intro h
    exact ⟨fun P hP => h P (Or.inl hP), fun P hP => h P (Or.inr hP)⟩
  · rintro ⟨hY, hZ⟩ P (hP | hP)
    · exact hY P hP
    · exact hZ P hP

/-- Hilbert's Nullstellensatz: for any ideal $I$ in $\overline{k}[x_1, \ldots, x_n]$,
$I(V(I)) = \sqrt{I}$. -/
theorem hilbert_nullstellensatz {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) (AlgebraicClosure k))) :
    idealOfAlgebraicSet (AlgebraicSet k n (I : Set _)) = I.radical := by
  rw [idealOfAlgebraicSet_eq_vanishingIdeal, algebraicSet_ideal_eq_zeroLocus,
    MvPolynomial.vanishingIdeal_zeroLocus_eq_radical]

