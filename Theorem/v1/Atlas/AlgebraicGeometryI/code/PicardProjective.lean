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


noncomputable section

namespace PicardProjective

open MvPolynomial


/-- A nonzero homogeneous polynomial has a unique degree of homogeneity. -/
lemma homogeneous_degree_unique {σ : Type*} {k : Type*} [Field k]
    {f : MvPolynomial σ k} {d₁ d₂ : ℕ}
    (hf : f ≠ 0) (h1 : f.IsHomogeneous d₁) (h2 : f.IsHomogeneous d₂) :
    d₁ = d₂ := by
  rw [Ne, MvPolynomial.ext_iff] at hf; push Not at hf
  obtain ⟨s, hs⟩ := hf; rw [MvPolynomial.coeff_zero] at hs
  linarith [h1 hs, h2 hs]

/-- Every unit in k[x_1,...,x_n] is a constant, hence homogeneous of degree 0. -/
lemma isUnit_isHomogeneous_zero {σ : Type*} {k : Type*} [Field k]
    {u : MvPolynomial σ k} (hu : IsUnit u) : u.IsHomogeneous 0 := by
  rw [MvPolynomial.isUnit_iff_eq_C_of_isReduced] at hu
  obtain ⟨r, _, rfl⟩ := hu; exact isHomogeneous_C σ r

/-- Associated homogeneous polynomials (i.e. differing by a unit) have the same
degree. -/
lemma associated_homogeneous_same_degree {σ : Type*} {k : Type*} [Field k]
    {f g : MvPolynomial σ k} {d₁ d₂ : ℕ}
    (hg : g ≠ 0) (hfh : f.IsHomogeneous d₁) (hgh : g.IsHomogeneous d₂)
    (h : Associated f g) : d₁ = d₂ := by
  obtain ⟨u, hu⟩ := h
  have : (f * u).IsHomogeneous (d₁ + 0) := hfh.mul (isUnit_isHomogeneous_zero u.isUnit)
  simp only [Nat.add_zero] at this; rw [hu] at this
  exact homogeneous_degree_unique hg this hgh

end PicardProjective
end
