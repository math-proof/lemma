/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/CMTorsor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.NumberTheory.Zsqrtd.Basic
import Mathlib.RingTheory.Norm.Defs
import Mathlib.RingTheory.Trace.Defs
import Mathlib.RingTheory.FractionalIdeal.Operations
import Mathlib.RingTheory.FractionalIdeal.Inverse
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.FractionalIdeal.Norm
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.LinearAlgebra.Quotient.Card
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Quotient.Pi
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.RingTheory.ClassGroup
import Def.v1.Atlas.EllipticCurves.code.ComplexMultiplication.Part6
import Lemma.Complex.Atlas.v1.EllipticCurves.code.ComplexMultiplication
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.RingTheory.Ideal.Colon
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.NumberTheory.NumberField.Basic
import Abbrev.v1.Atlas.EllipticCurves.code.CMTorsor


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
