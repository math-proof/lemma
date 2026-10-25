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
import Theorem.v1.Atlas.EllipticCurves.code.DivisionPolynomials.Part2
open Polynomial
open scoped Polynomial.Bivariate


namespace ShortWeierstrassCurve

variable {R : Type*} [CommRing R] (E : ShortWeierstrassCurve R)

/-- The $x$-coordinate numerator polynomial $\phi_n \in R[X][Y]$ used in the multiplication-by-$n$
map: $\phi_n = X \psi_n^2 - \psi_{n+1} \psi_{n-1}$. -/
noncomputable def phiPoly (n : ℤ) : R[X][Y] :=
  E.toWeierstrassCurve.φ n

/-- The numerator polynomial of $\omega_n$ (the $y$-coordinate piece of $[n]$), defined as
$\psi_{n+2}\psi_{n-1}^2 - \psi_{n-2}\psi_{n+1}^2$. -/
noncomputable def omegaPolyNumer (n : ℤ) : R[X][Y] :=
  E.divisionPoly (n + 2) * E.divisionPoly (n - 1) ^ 2 -
  E.divisionPoly (n - 2) * E.divisionPoly (n + 1) ^ 2

/-- Evaluate a bivariate polynomial $p \in S[X][Y]$ at a point $(x_0, y_0) \in S \times S$
by first specialising $Y \mapsto y_0$ then $X \mapsto x_0$. -/
def Polynomial.evalBivariate {S : Type*} [CommRing S]
    (p : Polynomial (Polynomial S)) (x₀ y₀ : S) : S :=
  (p.eval (Polynomial.C y₀)).eval x₀

namespace ShortWeierstrassCurve

variable {F : Type*} [Field F] [DecidableEq F] (E : ShortWeierstrassCurve F)

/-- Numeric evaluation of $\psi_n$ at the affine point $(x_0, y_0)$. -/
def evalDivisionPoly (n : ℤ) (x₀ y₀ : F) : F :=
  (E.divisionPoly n).evalBivariate x₀ y₀

/-- Numeric evaluation of $\phi_n$ at the affine point $(x_0, y_0)$. -/
def evalPhiPoly (n : ℤ) (x₀ y₀ : F) : F :=
  (E.phiPoly n).evalBivariate x₀ y₀

/-- Numeric evaluation of the $\omega_n$-numerator polynomial at $(x_0, y_0)$. -/
def evalOmegaNumer (n : ℤ) (x₀ y₀ : F) : F :=
  (E.omegaPolyNumer n).evalBivariate x₀ y₀

/-- The $x$-coordinate of $[n] P$ for $P = (x_0, y_0)$, given by $\phi_n / \psi_n^2$. -/
def mulByN_x (n : ℤ) (x₀ y₀ : F) : F :=
  E.evalPhiPoly n x₀ y₀ / (E.evalDivisionPoly n x₀ y₀) ^ 2

/-- Numeric value of $\omega_n(P) = \omega_n^{\mathrm{num}}/(4y_0)$ at the affine point
$P = (x_0, y_0)$. -/
def evalOmega (n : ℤ) (x₀ y₀ : F) : F :=
  E.evalOmegaNumer n x₀ y₀ / (4 * y₀)

/-- The $y$-coordinate of $[n] P$ for $P = (x_0, y_0)$, given by $\omega_n / \psi_n^3$. -/
def mulByN_y (n : ℤ) (x₀ y₀ : F) : F :=
  E.evalOmega n x₀ y₀ / (E.evalDivisionPoly n x₀ y₀) ^ 3

end ShortWeierstrassCurve
end ShortWeierstrassCurve
