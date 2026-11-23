/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/PolynomialDFS.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Def.v1.Atlas.GeometryOfManifolds.code.DifferentialForms.Part2
public import Theorem.Real.Atlas.v1.GeometryOfManifolds.code.DifferentialForms
public import Def.v1.Atlas.GeometryOfManifolds.code.PolynomialDFS.Part2
set_option autoImplicit false

public section

/-- Fundamental theorem of calculus for polynomials: $\frac{d}{dt} \int g(t)\, dt = g(t)$. -/
lemma derivative_antideriv (g : Polynomial ℝ) :
    Polynomial.derivative (polyAntideriv g) = g := by
  unfold polyAntideriv Polynomial.sum
  rw [Polynomial.derivative_sum]
  simp only [Polynomial.derivative_monomial, Nat.add_sub_cancel]
  have key : ∀ n ∈ g.support,
      (Polynomial.monomial n) (g.coeff n / ↑(n + 1) * ↑(n + 1)) =
      (Polynomial.monomial n) (g.coeff n) := by
    intro n _; congr 1; field_simp
  rw [Finset.sum_congr rfl key]
  conv_rhs => rw [g.as_sum_support]

