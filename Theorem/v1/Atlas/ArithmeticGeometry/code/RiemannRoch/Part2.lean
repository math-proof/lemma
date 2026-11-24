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
public import Instance.v1.Atlas.ArithmeticGeometry.code.RiemannRoch.Part2
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

variable [ConstantField k (O := O)]

/-- Pointwise formula for the $k$-action on adeles: $(c \cdot \alpha)_p = c \cdot \alpha_p$. -/
@[simp]
lemma smul_apply (c : k) (α : FunctionFieldAdeleRing F P O) (p : P) :
    (c • α) p = algebraMap k F c * α p := by
  simp only [Algebra.smul_def]; rfl

end FunctionFieldAdeleRing
