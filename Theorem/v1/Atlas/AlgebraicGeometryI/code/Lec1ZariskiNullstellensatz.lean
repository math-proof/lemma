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
import Def.v1.Atlas.AlgebraicGeometryI.code.Lec1ZariskiNullstellensatz
open MvPolynomial AlgebraicGeometry CategoryTheory


namespace Lec1ZariskiNullstellensatz

noncomputable section

/-- The vanishing ideal `I(V)` of any subset of affine space is a radical ideal. -/
lemma vanishingIdeal_isRadical (k : Type*) [Field k] (σ : Type*) (V : Set (σ → k)) :
    (MvPolynomial.vanishingIdeal k V).IsRadical := by
  intro f hf
  rw [Ideal.mem_radical_iff] at hf
  obtain ⟨n, hn⟩ := hf
  intro x hx
  have h := hn x hx
  rw [map_pow] at h
  exact eq_zero_of_pow_eq_zero h

/-- An ideal and its radical have the same zero locus: `V(I) = V(√I)`. -/
theorem zeroLocus_radical_eq (k : Type*) [Field k] (σ : Type*)
    (I : Ideal (MvPolynomial σ k)) :
    MvPolynomial.zeroLocus k I.radical = MvPolynomial.zeroLocus k I := by
  apply le_antisymm
  · exact MvPolynomial.zeroLocus_anti_mono Ideal.le_radical
  · intro x hx p hp
    rw [Ideal.mem_radical_iff] at hp
    obtain ⟨n, hn⟩ := hp
    have := hx _ hn
    rw [map_pow] at this
    exact eq_zero_of_pow_eq_zero this

end
end Lec1ZariskiNullstellensatz
