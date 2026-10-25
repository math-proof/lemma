/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ModularPolynomial.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Algebra.Polynomial.EraseLead
import Mathlib.Algebra.CharP.Defs
import Def.v1.Atlas.EllipticCurves.code.ModularCurves.Part3
import Lemma.Complex.Atlas.v1.EllipticCurves.code.ModularCurves
import Lemma.Complex.Atlas.v1.EllipticCurves.code.Uniformization
import Def.v1.Atlas.EllipticCurves.code.Uniformization
import Structure.v1.Atlas.EllipticCurves.code.ModularPolynomial
open scoped MatrixGroups UpperHalfPlane
open CongruenceSubgroup Complex


noncomputable section

open ModularFunction

namespace ModularPolynomial

/-- The (classical) modular polynomial `Φ_N(X, Y) ∈ ℤ[X, Y]` as a `MvPolynomial`
indexed by `Fin 2`, characterized in Definition 19.15 as the minimal polynomial of
`j_N` over `ℂ(j)`. -/
def HasCyclicNIsogeny (F : Type*) [Field F] (N : ℕ) (j₁ j₂ : F) : Prop :=
  ∃ (E₁ E₂ : WeierstrassCurve.Affine F) (_ : E₁.IsElliptic) (_ : E₂.IsElliptic),
    E₁.j = j₁ ∧ E₂.j = j₂ ∧
    ∃ (φ : E₁.Point →+ E₂.Point), Function.Surjective φ ∧
      ∃ (P : E₁.Point), addOrderOf P = N ∧
        ∀ Q : E₁.Point, φ Q = 0 → ∃ k : ℤ, Q = k • P

/-- Theorem 20.7: the modular polynomial is symmetric, `Φ_N(X, Y) = Φ_N(Y, X)`. -/
def dedekindPsi (N : ℕ) : ℕ :=
  if N = 0 then 0
  else ∏ p ∈ N.primeFactors, p ^ (N.factorization p - 1) * (p + 1)

/-- Theorem 19.14: the degree of `Φ_N` in the variable `Y` equals
`[Γ(1) : Γ₀(N)] = ψ(N)`. -/

end ModularPolynomial

namespace ModularFunction

/-- Corollary 19.10: every modular function for `Γ(1)` that is holomorphic on `ℍ` is a
polynomial in `j(τ)`. The witness `P` is constructed from a rational-function
representation by checking that the denominator polynomial has degree `0`. -/

end ModularFunction

section ModularCurveX0Defs

open UpperHalfPlane CongruenceSubgroup Matrix.SpecialLinearGroup Matrix

open scoped MatrixGroups UpperHalfPlane

/-- The `(i, j)`-entry of an `SL₂(ℤ)`-matrix, coerced to `ℚ`. -/
def sl2zEntry (γ : SL(2, ℤ)) (i j : Fin 2) : ℚ :=
  ((↑γ : Matrix (Fin 2) (Fin 2) ℤ) i j : ℚ)

end ModularCurveX0Defs
end
