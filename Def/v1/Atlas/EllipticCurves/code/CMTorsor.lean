module
public import Mathlib.NumberTheory.Zsqrtd.Basic
public import Mathlib.RingTheory.Norm.Defs
public import Mathlib.RingTheory.Trace.Defs
public import Mathlib.RingTheory.FractionalIdeal.Operations
public import Mathlib.RingTheory.FractionalIdeal.Inverse
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.RingTheory.FractionalIdeal.Norm
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.LinearAlgebra.Quotient.Card
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.Quotient.Pi
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.ZMod.QuotientRing
public import Mathlib.RingTheory.ClassGroup
public import Def.v1.Atlas.EllipticCurves.code.ComplexMultiplication.Part6
public import Theorem.Complex.Atlas.v1.EllipticCurves.code.ComplexMultiplication
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Ideal.Colon
public import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
public import Mathlib.NumberTheory.NumberField.Basic
public import Abbrev.v1.Atlas.EllipticCurves.code.CMTorsor


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/CMTorsor.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace FieldNormTrace

section Quadratic

variable {D : ℤ}

/-- The discriminant `t² - 4n` of a monic quadratic `x² - t x + n`. -/
def disc (t n : ℤ) : ℤ := t ^ 2 - 4 * n

/-- The integer trace of `τ ∈ ℤ√d`, defined as `2 · τ.re`. -/
def traceZ : ℤ := 2 * τ.re

/-- The discriminant of `τ ∈ ℤ√d`, given by `disc (traceZ τ) (N τ)`. -/
def discZsqrtd : ℤ := disc (traceZ τ) (Zsqrtd.norm τ)

/-- `D` is an imaginary quadratic discriminant if `D < 0` and `D ≡ 0` or `1 (mod 4)`. -/
def IsImaginaryQuadraticDiscriminant (D : ℤ) : Prop :=
  D < 0 ∧ (D % 4 = 0 ∨ D % 4 = 1)

/-- `D` is a fundamental imaginary quadratic discriminant if it is an imaginary quadratic
discriminant and is not of the form `u² · D'` for `u > 1` and another imaginary quadratic
discriminant `D'`. -/
def IsFundamentalImaginaryQuadraticDiscriminant (D : ℤ) : Prop :=
  IsImaginaryQuadraticDiscriminant D ∧
    ∀ u D' : ℤ, u > 1 → IsImaginaryQuadraticDiscriminant D' → D ≠ u ^ 2 * D'

end Quadratic
end FieldNormTrace
