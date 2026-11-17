/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Isogenies.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.LinearAlgebra.Projectivization.Basic
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.Algebra.Polynomial.RingDivision
public import Mathlib.Algebra.Squarefree.Basic
public import Structure.v1.Atlas.EllipticCurves.code.Isogenies.Part7

@[expose] public section

open Polynomial

open scoped Polynomial.Bivariate

universe u v


namespace IsogenyStandardForm

variable {F : Type u} [Field F]

namespace WithCurveData

variable (α : WithCurveData F)

/-- Convert a `HomogeneousTriple` into the `Fin 3 → MvPolynomial _ k` function
suitable for `MvPolynomial.bind₁`. -/
def HomogeneousTriple.toFun {k : Type u} [CommRing k]
    (t : HomogeneousTriple k) : Fin 3 → MvPolynomial (Fin 3) k :=
  ![t.ψ_x, t.ψ_y, t.ψ_z]

/-- Substitute the components of a homogeneous triple into a polynomial `f`,
i.e. compute `f(ψ_x, ψ_y, ψ_z)`. -/
noncomputable def HomogeneousTriple.substIn {k : Type u} [CommRing k]
    (t : HomogeneousTriple k) (f : MvPolynomial (Fin 3) k) : MvPolynomial (Fin 3) k :=
  MvPolynomial.bind₁ t.toFun f

end WithCurveData
end IsogenyStandardForm
