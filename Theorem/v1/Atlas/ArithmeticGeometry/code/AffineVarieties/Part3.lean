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
import Instance.v1.Atlas.ArithmeticGeometry.code.AffineVarieties.Part2
variable (k : Type*) [Field k]


section Theorem1221

open MvPolynomial

/-- Closure-like idempotence: $V(I(V(S))) = V(S)$ for any set of polynomials $S$. -/
theorem algebraicSet_idealOfAlgebraicSet_eq {n : ℕ}
    (S : Set (MvPolynomial (Fin n) (AlgebraicClosure k))) :
    AlgebraicSet k n ((idealOfAlgebraicSet (AlgebraicSet k n S)) : Set _) =
    AlgebraicSet k n S := by
  ext P
  simp only [AlgebraicSet, Set.mem_setOf_eq, mem_idealOfAlgebraicSet_iff, SetLike.mem_coe]
  exact ⟨fun hP f hfS => hP f (fun Q hQ => hQ f hfS), fun hP f hf => hf P hP⟩

/-- For an algebraic subset $V$, $V(I(V)) = V$. -/
theorem algebraicSet_idealOfAlgebraicSet_of_isAlgebraicSubset {n : ℕ}
    {V : Set (AffineSpace_k k n)} (hV : IsAlgebraicSubset k n V) :
    AlgebraicSet k n ((idealOfAlgebraicSet V) : Set _) = V := by
  obtain ⟨S, rfl⟩ := hV
  exact algebraicSet_idealOfAlgebraicSet_eq k S

/-- Theorem 12.21: an algebraic subset $V$ is irreducible iff $I(V)$ is a prime ideal. -/
theorem isIrreducibleAlgebraicSet_iff_isPrime {n : ℕ}
    {V : Set (AffineSpace_k k n)} (hV : IsAlgebraicSubset k n V) :
    IsIrreducibleAlgebraicSet k n V ↔ (idealOfAlgebraicSet V).IsPrime := by
  constructor
  ·
    intro hirr
    apply Ideal.IsPrime.mk
    ·
      intro h
      have h1 : (1 : MvPolynomial (Fin n) (AlgebraicClosure k)) ∈ idealOfAlgebraicSet V := by
        rw [h]; exact Submodule.mem_top
      obtain ⟨P, hP⟩ := hirr.1
      have := h1 P hP; simp at this
    ·
      intro f g hfg

      set V₁ := V ∩ {P | MvPolynomial.eval P f = 0}
      set V₂ := V ∩ {P | MvPolynomial.eval P g = 0}

      have hdecomp : V = V₁ ∪ V₂ := by
        ext P; simp only [V₁, V₂, Set.mem_union, Set.mem_inter_iff, Set.mem_setOf_eq]
        constructor
        · intro hP
          have := hfg P hP; rw [map_mul] at this
          rcases mul_eq_zero.mp this with h | h
          · exact Or.inl ⟨hP, h⟩
          · exact Or.inr ⟨hP, h⟩
        · rintro (⟨hP, -⟩ | ⟨hP, -⟩) <;> exact hP

      have hAlg1 : IsAlgebraicSubset k n V₁ := by
        obtain ⟨S, rfl⟩ := hV
        exact ⟨S ∪ {f}, by
          ext P; simp only [V₁, AlgebraicSet, Set.mem_inter_iff, Set.mem_setOf_eq,
            Set.mem_union, Set.mem_singleton_iff]
          exact ⟨fun ⟨hS, hf⟩ g => by rintro (hg | rfl) <;> [exact hS g hg; exact hf],
                 fun h => ⟨fun g hg => h g (.inl hg), h f (.inr rfl)⟩⟩⟩

      have hAlg2 : IsAlgebraicSubset k n V₂ := by
        obtain ⟨S, rfl⟩ := hV
        exact ⟨S ∪ {g}, by
          ext P; simp only [V₂, AlgebraicSet, Set.mem_inter_iff, Set.mem_setOf_eq,
            Set.mem_union, Set.mem_singleton_iff]
          exact ⟨fun ⟨hS, hg⟩ p => by rintro (hp | rfl) <;> [exact hS p hp; exact hg],
                 fun h => ⟨fun p hp => h p (.inl hp), h g (.inr rfl)⟩⟩⟩

      rcases hirr.2 V₁ V₂ hAlg1 hAlg2 hdecomp with h | h
      ·
        left; rw [mem_idealOfAlgebraicSet_iff]; intro P hP
        exact (h.symm ▸ hP : P ∈ V₁).2
      ·
        right; rw [mem_idealOfAlgebraicSet_iff]; intro P hP
        exact (h.symm ▸ hP : P ∈ V₂).2
  ·
    intro hprime
    constructor
    ·
      by_contra hempty
      rw [Set.not_nonempty_iff_eq_empty] at hempty
      apply hprime.ne_top; ext f; simp only [Submodule.mem_top, iff_true]
      rw [mem_idealOfAlgebraicSet_iff]; intro P hP
      simp [hempty] at hP
    ·
      intro V₁ V₂ hV₁ hV₂ hunion

      have hIV : idealOfAlgebraicSet V = idealOfAlgebraicSet V₁ ⊓ idealOfAlgebraicSet V₂ := by
        rw [hunion, idealOfAlgebraicSet_union]
      have hmul : idealOfAlgebraicSet V₁ * idealOfAlgebraicSet V₂ ≤ idealOfAlgebraicSet V :=
        hIV ▸ Ideal.mul_le_inf

      rw [hprime.mul_le] at hmul

      have hle1 : idealOfAlgebraicSet V ≤ idealOfAlgebraicSet V₁ :=
        idealOfAlgebraicSet_anti_mono (hunion ▸ Set.subset_union_left)
      have hle2 : idealOfAlgebraicSet V ≤ idealOfAlgebraicSet V₂ :=
        idealOfAlgebraicSet_anti_mono (hunion ▸ Set.subset_union_right)

      rcases hmul with h | h
      · left
        have heq : idealOfAlgebraicSet V₁ = idealOfAlgebraicSet V := le_antisymm h hle1
        rw [← algebraicSet_idealOfAlgebraicSet_of_isAlgebraicSubset k hV₁,
            ← algebraicSet_idealOfAlgebraicSet_of_isAlgebraicSubset k hV]
        congr 1; exact_mod_cast heq
      · right
        have heq : idealOfAlgebraicSet V₂ = idealOfAlgebraicSet V := le_antisymm h hle2
        rw [← algebraicSet_idealOfAlgebraicSet_of_isAlgebraicSubset k hV₂,
            ← algebraicSet_idealOfAlgebraicSet_of_isAlgebraicSubset k hV]
        congr 1; exact_mod_cast heq

end Theorem1221

section Corollary1218

open MvPolynomial

variable {n : ℕ}

/-- The vanishing ideal $I(V)$ of any subset $V$ is always a radical ideal. -/
theorem idealOfAlgebraicSet_isRadical
    (V : Set (AffineSpace_k k n)) :
    (idealOfAlgebraicSet V).IsRadical := by
  rw [idealOfAlgebraicSet_eq_vanishingIdeal]
  have hgc := @MvPolynomial.zeroLocus_vanishingIdeal_galoisConnection (AlgebraicClosure k)
    (AlgebraicClosure k) _ _ _ (Fin n)
  rw [Ideal.IsRadical]
  rw [← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical
      (k := AlgebraicClosure k) (K := AlgebraicClosure k)
      (MvPolynomial.vanishingIdeal (AlgebraicClosure k) V)]
  rw [hgc.u_l_u_eq_u V]

/-- If $I$ is radical, then $I(V(I)) = I$ (consequence of the Nullstellensatz). -/
theorem idealOfAlgebraicSet_algebraicSet_of_isRadical
    (I : Ideal (MvPolynomial (Fin n) (AlgebraicClosure k)))
    (hI : I.IsRadical) :
    idealOfAlgebraicSet (AlgebraicSet k n (I : Set _)) = I := by
  rw [hilbert_nullstellensatz, hI.radical]

end Corollary1218
