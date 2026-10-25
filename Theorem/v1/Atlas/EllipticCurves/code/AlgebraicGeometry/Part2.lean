/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/AlgebraicGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.Nullstellensatz
import Mathlib.Topology.Irreducible
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.FieldTheory.Perfect
import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Def.v1.Atlas.EllipticCurves.code.AlgebraicGeometry.Part5
open MvPolynomial Set


noncomputable section

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

variable {σ : Type*}

/-- The union of two algebraic sets is algebraic, realized via the
intersection of their defining ideals. -/
theorem isAffineAlgebraicSet_union {V₁ V₂ : Set (σ → K)}
    (h₁ : IsAffineAlgebraicSet K V₁) (h₂ : IsAffineAlgebraicSet K V₂) :
    IsAffineAlgebraicSet K (V₁ ∪ V₂) := by
  obtain ⟨I, rfl⟩ := h₁
  obtain ⟨J, rfl⟩ := h₂
  exact ⟨I ⊓ J, by
    ext x
    simp only [Set.mem_union, MvPolynomial.mem_zeroLocus_iff, Ideal.mem_inf]
    constructor
    · rintro (h | h) p ⟨hp1, hp2⟩
      · exact h p hp1
      · exact h p hp2
    · intro h
      by_contra hc
      push Not at hc
      obtain ⟨⟨p, hp, hpx⟩, ⟨q, hq, hqx⟩⟩ := hc
      have hpq : p * q ∈ I ⊓ J :=
        Ideal.mem_inf.mpr ⟨I.mul_mem_right q hp, J.mul_mem_left p hq⟩
      have := h (p * q) hpq
      rw [map_mul] at this
      exact (mul_eq_zero.mp this).elim hpx hqx⟩

/-- An arbitrary intersection of algebraic sets is algebraic, realized via
the supremum of the corresponding ideals. -/
theorem isAffineAlgebraicSet_sInter (A : Set (Set (σ → K)))
    (hA : ∀ V ∈ A, IsAffineAlgebraicSet K V) :
    IsAffineAlgebraicSet K (⋂₀ A) := by
  choose I hI using hA
  exact ⟨⨆ V : A, I V.1 V.2, by
    ext x
    simp only [Set.mem_sInter, MvPolynomial.mem_zeroLocus_iff]
    constructor
    · intro h p hp
      have : ∀ (V : A), I V.1 V.2 ≤ RingHom.ker (aeval (R := K) x) := by
        intro ⟨V, hV⟩ q hq
        simp only [RingHom.mem_ker]
        have := h V hV
        rw [hI V hV] at this
        exact this q hq
      have hsup := iSup_le this
      simpa [RingHom.mem_ker] using hsup hp
    · intro h V hV
      rw [hI V hV]
      intro p hp'
      exact h p (Ideal.mem_iSup_of_mem ⟨V, hV⟩ hp')⟩

end
