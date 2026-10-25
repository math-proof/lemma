/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec1ZariskiNullstellensatz.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.Order.KrullDimension
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Theorem.v1.Atlas.AlgebraicGeometryI.code.Lec1ZariskiNullstellensatz
open MvPolynomial AlgebraicGeometry CategoryTheory


namespace Lec1ZariskiNullstellensatz

noncomputable section

/-- Theorem 1.2 (Lecture 1). Over an algebraically closed field with finitely many variables,
there is a bijection between radical ideals of `k[x_σ]` and Zariski-closed subsets of `k^σ`,
given by `I ↦ V(I)` with inverse `V ↦ I(V)`. -/
noncomputable def nullstellensatz_bijection
    (k : Type*) [Field k] [IsAlgClosed k] (σ : Type*) [Finite σ] :
    {I : Ideal (MvPolynomial σ k) // I.IsRadical} ≃
      {V : Set (σ → k) // ∃ I : Ideal (MvPolynomial σ k), V = MvPolynomial.zeroLocus k I} := by
  refine ⟨
    fun ⟨I, _⟩ => ⟨MvPolynomial.zeroLocus k I, ⟨I, rfl⟩⟩,
    fun ⟨V, _⟩ => ⟨MvPolynomial.vanishingIdeal k V, vanishingIdeal_isRadical k σ V⟩,
    ?_, ?_⟩
  ·
    rintro ⟨I, hI⟩
    exact Subtype.ext
      ((MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := k) I).trans hI.radical)
  ·
    rintro ⟨V, I, rfl⟩
    apply Subtype.ext
    show MvPolynomial.zeroLocus k
      (MvPolynomial.vanishingIdeal k (MvPolynomial.zeroLocus k I)) =
      MvPolynomial.zeroLocus k I
    rw [MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := k) I, zeroLocus_radical_eq]

end
end Lec1ZariskiNullstellensatz
