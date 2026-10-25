/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Proposition_1_27_1.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.Coalgebra.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.Quotient.Basic
universe u


noncomputable section

namespace EGNO.Prop1271

/-- An element `g` of a coalgebra is grouplike if `Δ(g) = g ⊗ g` and `ε(g) = 1`. -/
def IsGrouplike {R : Type*} {C : Type*} [CommSemiring R] [AddCommMonoid C] [Module R C]
    [Coalgebra R C] (g : C) : Prop :=
  Coalgebra.comul (R := R) g = g ⊗ₜ g ∧ Coalgebra.counit (R := R) g = 1

/-- An element `x` of a coalgebra is skew-primitive of type `(g, h)` if
`Δ(x) = x ⊗ g + h ⊗ x` (Definition 1.24.6). -/
def IsSkewPrimitive {R : Type*} {C : Type*} [CommSemiring R] [AddCommMonoid C] [Module R C]
    [Coalgebra R C] (g h x : C) : Prop :=
  Coalgebra.comul (R := R) x = x ⊗ₜ g + h ⊗ₜ x

/-- The submodule of skew-primitive elements `Prim_{g,h}(C)` of a coalgebra. -/
def skewPrimitiveSpace {R : Type*} {C : Type*} [CommSemiring R] [AddCommGroup C] [Module R C]
    [Coalgebra R C] (g h : C) : Submodule R C where
  carrier := {x : C | IsSkewPrimitive (R := R) g h x}
  add_mem' {x y} hx hy := by
    simp only [Set.mem_setOf_eq] at *
    unfold IsSkewPrimitive at *
    rw [map_add, hx, hy, TensorProduct.add_tmul, TensorProduct.tmul_add]; abel
  zero_mem' := by
    simp only [Set.mem_setOf_eq]; unfold IsSkewPrimitive
    simp [TensorProduct.zero_tmul, TensorProduct.tmul_zero]
  smul_mem' r x hx := by
    simp only [Set.mem_setOf_eq] at *
    unfold IsSkewPrimitive at *
    rw [LinearMap.map_smul, hx]
    simp [TensorProduct.smul_tmul', TensorProduct.tmul_smul]


section TrivialSkewPrimitive

variable {k : Type u} {C : Type u} [Field k] [AddCommGroup C] [Module k C] [Coalgebra k C]

/-- The "trivial" skew-primitive subspace `k(h - g)` whose quotient in
`skewPrimitiveSpace g h` is identified with `Ext¹(g, h)`. -/
def trivialSkewPrimitiveSubspace (g h : C) : Submodule k C :=
  Submodule.span k {h - g}

end TrivialSkewPrimitive
end EGNO.Prop1271
end
