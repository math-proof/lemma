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
public import Def.v1.Atlas.ArithmeticGeometry.code.RiemannRoch
open scoped RestrictedProduct


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/RiemannRoch.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
variable {F : Type*} [Field F] {P : Type*} {O : P → ValuationSubring F}


namespace FunctionFieldAdeleRing

/-- The adele ring inherits a commutative ring structure from the restricted product. -/
noncomputable instance instCommRing : CommRing (FunctionFieldAdeleRing F P O) :=
  inferInstanceAs (CommRing (Πʳ _p : P, [(fun _ => F) _p, (O _p : ValuationSubring F)]))

/-- Adeles act as functions $P \to F$ via the underlying restricted product. -/
instance instDFunLike :
    DFunLike (FunctionFieldAdeleRing F P O) P (fun _ => F) :=
  inferInstanceAs <|
    DFunLike (Πʳ _p : P, [(fun _ => F) _p, (O _p : ValuationSubring F)]) P (fun _ => F)

end FunctionFieldAdeleRing
