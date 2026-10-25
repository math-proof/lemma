/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/DivisionPolynomials.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import Mathlib.Tactic.LinearCombination
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.RingTheory.Polynomial.Wronskian
import Mathlib.FieldTheory.SeparableDegree
import Def.v1.Atlas.EllipticCurves.code.IsogenyKernels.Part4
import Lemma.Complex.Atlas.v1.EllipticCurves.code.IsogenyKernels
import Lemma.Complex.Atlas.v1.EllipticCurves.code.Isogenies
import Lemma.Complex.Atlas.v1.EllipticCurves.code.TorsionEndomorphism
import Def.v1.Atlas.EllipticCurves.code.Isogenies.Part13
import Lemma.Complex.Atlas.v1.EllipticCurves.code.Lemma53
import Def.v1.Atlas.EllipticCurves.code.TorsionEndomorphism.Part3
import Inductive.v1.Atlas.EllipticCurves.code.DivisionPolynomials
open Polynomial
open scoped Polynomial.Bivariate


namespace ShortWeierstrassCurve

variable {R : Type*} [CommRing R] (E : ShortWeierstrassCurve R)

open Polynomial

open WeierstrassCurve.Affine in
/-- The compose of an `IsogenyChain` as an additive group homomorphism on point groups. -/
def IsogenyChain.compose {F : Type*} [Field F] [DecidableEq F]
    {E₁ E₂ : WeierstrassCurve.Affine F} :
    IsogenyChain E₁ E₂ → (E₁.Point →+ E₂.Point)
  | .single φ => φ.toAddMonoidHom
  | .cons φ rest => rest.compose.comp φ.toAddMonoidHom

open WeierstrassCurve.Affine in
/-- Predicate asserting that every link in an `IsogenyChain` has prime degree. -/
def IsogenyChain.allPrimeDegree {F : Type*} [Field F] [DecidableEq F]
    {E₁ E₂ : WeierstrassCurve.Affine F} :
    IsogenyChain E₁ E₂ → Prop
  | .single φ => Nat.Prime φ.degree
  | .cons φ rest => Nat.Prime φ.degree ∧ rest.allPrimeDegree

/-- Public alias for the $n$-th division polynomial of a short Weierstrass curve. -/
noncomputable def psi {R : Type*} [CommRing R] (E : ShortWeierstrassCurve R) (n : ℤ) :
    R[X][Y] :=
  E.divisionPoly n

/-- Public alias for the $n$-th $\phi$-polynomial of a short Weierstrass curve. -/
noncomputable def phi {R : Type*} [CommRing R] (E : ShortWeierstrassCurve R) (n : ℤ) :
    R[X][Y] :=
  E.phiPoly n

/-- Public alias for the numerator of the $n$-th $\omega$-polynomial. -/
noncomputable def omegaNumer {R : Type*} [CommRing R] (E : ShortWeierstrassCurve R) (n : ℤ) :
    R[X][Y] :=
  E.omegaPolyNumer n

section BaseCases

variable {R : Type*} [CommRing R] (E : ShortWeierstrassCurve R)

/-- Numerical evaluation of $\psi_n$ at the affine point $(x_0, y_0)$. -/
def evalPsi (n : ℤ) (x₀ y₀ : F) : F := E.evalDivisionPoly n x₀ y₀

/-- Numerical evaluation of $\phi_n$ at the affine point $(x_0, y_0)$. -/
def evalPhi (n : ℤ) (x₀ y₀ : F) : F := E.evalPhiPoly n x₀ y₀

/-- Numerical evaluation of $\omega_n$ at the affine point $(x_0, y_0)$. -/
def evalOmega (n : ℤ) (x₀ y₀ : F) : F := E.evalOmega n x₀ y₀

/-- $x$-coordinate of $[n] P$ for $P = (x_0, y_0)$, as $\phi_n(P) / \psi_n(P)^2$. -/
def mulByN_x (n : ℤ) (x₀ y₀ : F) : F := E.mulByN_x n x₀ y₀

/-- $y$-coordinate of $[n] P$ for $P = (x_0, y_0)$, as $\omega_n(P) / \psi_n(P)^3$. -/
def mulByN_y (n : ℤ) (x₀ y₀ : F) : F := E.mulByN_y n x₀ y₀

end BaseCases
end ShortWeierstrassCurve
