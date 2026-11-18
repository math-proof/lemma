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
public import Theorem.v1.Atlas.ArithmeticGeometry.code.RiemannRoch.Part2
public section
open scoped RestrictedProduct

variable {F : Type*} [Field F] {P : Type*} {O : P → ValuationSubring F}

namespace FunctionFieldAdeleRing

variable [ConstantField k (O := O)]

/-- Assumed: from a family $(O_p)_{p \in P}$ of valuation subrings of $F$ one obtains the
function-field-curve structure on $P$ used elsewhere. -/
class FunctionFieldProperty (F : Type*) (P : Type*) [Field F]
    (O : P → ValuationSubring F) extends FunctionFieldCurve P F

/-- Default instance deriving `FunctionFieldProperty` from a family of valuation subrings. -/
class DiscreteValuationFamily (P : Type*) (F : Type*) (k : Type*)
    [Field k] [Field F] [Algebra k F] where
  ord : P → F → WithTop ℤ
  ord_zero : ∀ p, ord p 0 = ⊤
  uniformizer_exists : ∀ p, ∃ t : F, ord p t = (1 : ℤ)
  ord_add_ge_min : ∀ (p : P) (x y : F),
    ord p (x + y) ≥ min (ord p x) (ord p y)
  ord_algebraMap : ∀ (p : P) (c : k), c ≠ 0 → ord p (algebraMap k F c) = (0 : ℤ)
  ord_mul : ∀ (p : P) (x y : F), ord p (x * y) = ord p x + ord p y

end FunctionFieldAdeleRing
