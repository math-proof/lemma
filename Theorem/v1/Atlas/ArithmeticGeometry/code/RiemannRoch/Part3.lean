/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/RiemannRoch.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Set.Algebra.RestrictedProduct.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Def.v1.Atlas.ArithmeticGeometry.code.EffectiveDivisors
public import Theorem.Scheme.Atlas.v1.ArithmeticGeometry.code.EffectiveDivisors
public import Theorem.Scheme.Atlas.v1.ArithmeticGeometry.code.CanonicalDivisors
public import Def.v1.Atlas.ArithmeticGeometry.code.CanonicalDivisors.Part2
public import Class.v1.Atlas.ArithmeticGeometry.code.RiemannRoch.Part3
open scoped RestrictedProduct

public section

variable {F : Type*} [Field F] {P : Type*} {O : P → ValuationSubring F}


/-- Axiom form: constants $c \in k^\times$ have order zero at every point $P \in C$. -/
theorem RiemannRochData.ord_algebraMap_eq_ax {C : Type*} {F : Type*} {k : Type*}
    [Field k] [Field F] [Algebra k F] [RiemannRochData C F k]
    (P : C) (c : kˣ) :
    CurveWithOrd.ord P (Units.map (algebraMap k F).toMonoidHom c) = 0 :=
  CurveWithConstants.ord_constant P c

/-- Ultrametric inequality for sums of nonzero elements at a point: when $f + g \ne 0$,
$\operatorname{ord}_P(f + g) \ge \min(\operatorname{ord}_P(f), \operatorname{ord}_P(g))$. -/
theorem RiemannRochData.ord_add_ge_min_field {C : Type*} {F : Type*} {k : Type*}
    [Field k] [Field F] [Algebra k F] [RiemannRochData C F k]
    (P : C) (f g : Fˣ) (hfg : (f : F) + (g : F) ≠ 0) :
    CurveWithOrd.ord P (Units.mk0 ((f : F) + (g : F)) hfg) ≥
      min (CurveWithOrd.ord P f) (CurveWithOrd.ord P g) :=
  CurveWithOrd.ord_add P f g hfg
