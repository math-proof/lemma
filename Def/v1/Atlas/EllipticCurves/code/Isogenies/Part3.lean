/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Isogenies.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Squarefree.Basic
import Structure.v1.Atlas.EllipticCurves.code.Isogenies.Part2
open Polynomial

open scoped Polynomial.Bivariate

universe u v


namespace ProjectiveCurve

variable {k : Type u} [CommRing k]

/-- Evaluation ring homomorphism from the coordinate ring `k[X][Y]/(f₀)` to the
base ring `k` induced by an affine point `P`. -/
noncomputable def AffinePoint.evalRingHom {f₀ : k[X][Y]} (P : AffinePoint f₀) :
    CoordinateRing f₀ →+* k :=
  AdjoinRoot.lift (Polynomial.evalRingHom P.x) P.y P.on_curve

/-- Coerce a `k`-rational affine point into an affine point over `k` viewed as a
`k`-algebra. -/
def AffinePoint.toOver {f₀ : k[X][Y]} (P : AffinePoint f₀) : AffinePointOver f₀ k where
  x := P.x
  y := P.y
  on_curve := by rw [eval₂RingHom_algebraMap_self]; exact P.on_curve

/-- A function `φ` on the curve is regular at an `L`-point `P` if it can be written
as `g/h` with `h` not vanishing at `P`. -/
def FunctionField.IsRegularAtOver {f₀ : k[X][Y]} {L : Type v} [CommRing L] [Algebra k L]
    (φ : FunctionField f₀) (P : AffinePointOver f₀ L) : Prop :=
  ∃ (g : CoordinateRing f₀) (h : ↥(nonZeroDivisors (CoordinateRing f₀))),
    φ = IsLocalization.mk' (FunctionField f₀) g h ∧
    P.evalRingHom (h : CoordinateRing f₀) ≠ 0

/-- A function on the curve is regular at a `k`-rational affine point `P` if it
admits a representation `g/h` with `h(P) ≠ 0`. -/
def FunctionField.IsRegularAt {f₀ : k[X][Y]}
    (φ : FunctionField f₀) (P : AffinePoint f₀) : Prop :=
  ∃ (g : CoordinateRing f₀) (h : ↥(nonZeroDivisors (CoordinateRing f₀))),
    φ = IsLocalization.mk' (FunctionField f₀) g h ∧
    P.evalRingHom (h : CoordinateRing f₀) ≠ 0

/-- A function `φ` is regular and nonzero at a `k`-rational affine point `P` if it
has a representation `g/h` with `h(P) ≠ 0` and `g(P) ≠ 0`. -/
def FunctionField.IsRegularNonzeroAt {f₀ : k[X][Y]}
    (φ : FunctionField f₀) (P : AffinePoint f₀) : Prop :=
  ∃ (g : CoordinateRing f₀) (h : ↑(nonZeroDivisors (CoordinateRing f₀))),
    φ = IsLocalization.mk' (FunctionField f₀) g h ∧
    P.evalRingHom (h : CoordinateRing f₀) ≠ 0 ∧
    P.evalRingHom g ≠ 0

set_option synthInstance.maxHeartbeats 40000 in
/-- Bivariate evaluation: evaluate `f ∈ k[X][Y]` at scalars `(a, b) ∈ R × R` for a
`k`-algebra `R`, by mapping coefficients via `algebraMap k R`. -/
noncomputable def evalBivariate {R : Type u} [CommRing R] [Algebra k R]
    (f : k[X][Y]) (a b : R) : R :=
  Polynomial.eval₂ (Polynomial.eval₂RingHom (algebraMap k R) a) b f

end ProjectiveCurve
