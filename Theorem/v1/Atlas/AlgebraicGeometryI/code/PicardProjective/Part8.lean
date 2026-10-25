/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/PicardProjective.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.UniqueFactorizationDomain.ClassGroup
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Def.v1.Atlas.AlgebraicGeometryI.code.PicardProjective.Part6


noncomputable section

namespace PicardProjective

open MvPolynomial


/-- The degree homomorphism Pic(P^n) → ℤ is surjective (every integer is realized by
some O(d)). -/
lemma degreeHom_surjective (n : ℕ) (k : Type*) [Field k] :
    Function.Surjective (GradedPicardGroup.degreeHom (Fin (n + 1)) k) := by
  intro d
  exact ⟨twistingSheafPow n k d, by
    simp only [GradedPicardGroup.degreeHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
    exact twistFraction_degree n k d⟩

/-- The degree homomorphism is injective: any line bundle of degree 0 is trivial. -/
lemma degreeHom_injective (σ : Type*) (k : Type*) [Field k] :
    Function.Injective (GradedPicardGroup.degreeHom σ k) := by
  intro x y hxy
  induction x using Quotient.ind
  induction y using Quotient.ind
  apply Quotient.sound
  rename_i p q
  have hpq : p.degree σ k = q.degree σ k := hxy


  have hdeq : p.ndeg + q.ddeg = q.ndeg + p.ddeg := by
    unfold HomogFraction.degree at hpq; omega
  refine ⟨p.num * q.den, q.num * p.den,
    p.ndeg + q.ddeg, q.ndeg + p.ddeg,
    mul_ne_zero p.num_ne q.den_ne, mul_ne_zero q.num_ne p.den_ne,
    p.nhom.mul q.dhom, q.nhom.mul p.dhom, hdeq, ?_⟩
  have : p.num * (q.num * p.den) * q.den = q.num * (p.num * q.den) * p.den := by ring
  rw [this]


end PicardProjective
end
