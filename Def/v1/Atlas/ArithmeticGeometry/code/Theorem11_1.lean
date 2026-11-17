/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Theorem11_1.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.Padics.Hensel
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.FieldTheory.ChevalleyWarning
public import Mathlib.Algebra.MvPolynomial.Degrees

@[expose] public section

noncomputable section

open PadicInt Polynomial

variable {p : ℕ} [hp : Fact p.Prime]

/-- The diagonal quadratic multivariate polynomial $\sum_i a_i X_i^2$ over $\mathbb{Z}/p$. -/
def diagQuadMvPoly {n : ℕ} (a : Fin n → ZMod p) :
    MvPolynomial (Fin n) (ZMod p) :=
  ∑ i : Fin n, MvPolynomial.C (a i) * (MvPolynomial.X i) ^ 2

/-- The univariate quadratic polynomial $c + a X^2 \in \mathbb{Z}_p[X]$. -/
def quadPoly (a c : ℤ_[p]) : Polynomial ℤ_[p] :=
  Polynomial.C c + Polynomial.C a * Polynomial.X ^ 2

end
