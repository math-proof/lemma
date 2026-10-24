/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/FieldTheory/SeparableAdjoinRoot.lean -/


import Lemma.Int.SeparableAdjoinRoot

set_option autoImplicit false

open scoped Polynomial

namespace Algebra

variable (K L : Type*) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]

/-- Forward use: a separable extension yields its generating polynomial. -/
example (h : Algebra.IsSeparable K L) :
    ∃ f : K[X], f.Monic ∧ Irreducible f ∧ f.Separable ∧
      Nonempty (L ≃ₐ[K] AdjoinRoot f) :=
  (isSeparable_iff_exists_monic_irreducible_separable K L).mp h

/-- Reverse use: a suitable polynomial witness implies separability. -/
example (f : K[X]) (hfM : f.Monic) (hfI : Irreducible f) (hfS : f.Separable)
    (he : Nonempty (L ≃ₐ[K] AdjoinRoot f)) : Algebra.IsSeparable K L :=
  (isSeparable_iff_exists_monic_irreducible_separable K L).mpr ⟨f, hfM, hfI, hfS, he⟩

/-- Project the monic condition out of the witness. -/
example (h : Algebra.IsSeparable K L) :
    ∃ f : K[X], f.Monic ∧ Nonempty (L ≃ₐ[K] AdjoinRoot f) := by
  obtain ⟨f, hfM, _, _, he⟩ :=
    (isSeparable_iff_exists_monic_irreducible_separable K L).mp h
  exact ⟨f, hfM, he⟩

/-- Project the irreducibility condition out of the witness. -/
example (h : Algebra.IsSeparable K L) :
    ∃ f : K[X], Irreducible f ∧ Nonempty (L ≃ₐ[K] AdjoinRoot f) := by
  obtain ⟨f, _, hfI, _, he⟩ :=
    (isSeparable_iff_exists_monic_irreducible_separable K L).mp h
  exact ⟨f, hfI, he⟩

/-- Project the separability condition out of the witness. -/
example (h : Algebra.IsSeparable K L) :
    ∃ f : K[X], f.Separable ∧ Nonempty (L ≃ₐ[K] AdjoinRoot f) := by
  obtain ⟨f, _, _, hfS, he⟩ :=
    (isSeparable_iff_exists_monic_irreducible_separable K L).mp h
  exact ⟨f, hfS, he⟩

/-- Round trip through the equivalence. -/
example (h : Algebra.IsSeparable K L) : Algebra.IsSeparable K L := by
  have hw := (isSeparable_iff_exists_monic_irreducible_separable K L).mp h
  exact (isSeparable_iff_exists_monic_irreducible_separable K L).mpr hw

end Algebra
