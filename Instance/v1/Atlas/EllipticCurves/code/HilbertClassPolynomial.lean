module
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Polynomial.Degree.Operations
public import Mathlib.Algebra.Polynomial.Lifts
public import Mathlib.Data.Complex.Basic
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.RingTheory.Algebraic.Basic
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.NumberTheory.Niven
public import Mathlib.RingTheory.Polynomial.Vieta
public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.GroupTheory.GroupAction.Basic
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.Algebra.Polynomial.Bivariate
public import Def.v1.Atlas.EllipticCurves.code.ComplexMultiplication.Part6
public import Theorem.Complex.Atlas.v1.EllipticCurves.code.ComplexMultiplication
public import Def.v1.Atlas.EllipticCurves.code.HilbertClassPolynomial


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/HilbertClassPolynomial.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
noncomputable section

open Polynomial Classical

/-- Typeclass-level commutative group instance on `cl(𝒪)`. -/
noncomputable instance (D : ℤ) (hD : IsImaginaryQuadraticDiscriminant D) :
    CommGroup (ImagQuadIdealClass D hD) := instCommGroupImagQuadIdealClass D hD

end
