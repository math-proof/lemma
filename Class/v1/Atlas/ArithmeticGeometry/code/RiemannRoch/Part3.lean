module

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/RiemannRoch.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

public import Mathlib.Set.Algebra.RestrictedProduct.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Def.v1.Atlas.ArithmeticGeometry.code.EffectiveDivisors
public import Def.v1.Atlas.ArithmeticGeometry.code.CanonicalDivisors.Part2
public import Def.v1.Atlas.ArithmeticGeometry.code.RiemannRoch.Part3
public section
open scoped RestrictedProduct

variable {F : Type*} [Field F] {P : Type*} {O : P → ValuationSubring F}

/-- The complete data structure for a curve $C$ with function field $F$ and constant
subfield $k$ needed to prove Riemann-Roch: a `CurveWithConstants` together with all
ancillary structure used in the proof. -/
class RiemannRochData (C : Type*) (F : Type*) (k : Type*)
    [Field k] [Field F] [Algebra k F] extends CurveWithConstants C k F

