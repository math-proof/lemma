/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/AlgebraicNumbers.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Complex.Basic
public import Mathlib.RingTheory.Algebraic.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
public import Mathlib.NumberTheory.NumberField.Basic

@[expose] public section


namespace AlgebraicNumber

/-- A complex number is an algebraic number if it is algebraic over the rationals `ℚ`. -/
abbrev IsAlgebraicNumber (α : ℂ) : Prop := IsAlgebraic ℚ α

/-- A complex number is an algebraic integer if it is integral over `ℤ`, i.e. it is the
root of a monic polynomial with integer coefficients. -/
abbrev IsAlgebraicInteger (α : ℂ) : Prop := IsIntegral ℤ α

end AlgebraicNumber
