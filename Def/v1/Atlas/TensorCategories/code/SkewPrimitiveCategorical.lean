/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/SkewPrimitiveCategorical.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.FGModuleCat.Basic
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.CategoryTheory.Simple
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Spectrum.Maximal.Basic
set_option maxHeartbeats 800000

open Coalgebra
open scoped TensorProduct
open CategoryTheory MonoidalCategory Category Limits

universe v u w


noncomputable section

/-- An element `g` of a coalgebra is grouplike when `Δ g = g ⊗ g` and `ε g = 1`. -/
def IsGrouplike {R : Type*} {C : Type*} [CommSemiring R] [AddCommMonoid C] [Module R C]
    [Coalgebra R C] (g : C) : Prop :=
  Coalgebra.comul (R := R) g = g ⊗ₜ g ∧ Coalgebra.counit (R := R) g = 1

/-- An element `x` of a coalgebra is `(g, h)`-skew-primitive when its comultiplication
satisfies `Δ x = x ⊗ g + h ⊗ x`. -/
def IsSkewPrimitive {R : Type*} {C : Type*} [CommSemiring R] [AddCommMonoid C] [Module R C]
    [Coalgebra R C] (g h x : C) : Prop :=
  Coalgebra.comul (R := R) x = x ⊗ₜ g + h ⊗ₜ x

/-- The `R`-submodule of all `(g, h)`-skew-primitive elements of a coalgebra `C`. -/
def skewPrimitiveSpace {R : Type*} {C : Type*} [CommSemiring R] [AddCommGroup C] [Module R C]
    [Coalgebra R C] (g h : C) : Submodule R C where
  carrier := {x : C | IsSkewPrimitive (R := R) g h x}
  add_mem' {x y} hx hy := by
    simp only [Set.mem_setOf_eq] at *
    unfold IsSkewPrimitive at *
    rw [map_add, hx, hy, TensorProduct.add_tmul, TensorProduct.tmul_add]
    abel
  zero_mem' := by
    simp only [Set.mem_setOf_eq]
    unfold IsSkewPrimitive
    simp [TensorProduct.zero_tmul, TensorProduct.tmul_zero]
  smul_mem' r x hx := by
    simp only [Set.mem_setOf_eq] at *
    unfold IsSkewPrimitive at *
    rw [LinearMap.map_smul, hx]
    simp [TensorProduct.smul_tmul', TensorProduct.tmul_smul]


namespace HopfAlgebra

/-- An element `x` of a bialgebra is primitive when `Δ x = x ⊗ 1 + 1 ⊗ x`; equivalently, a
`(1, 1)`-skew-primitive element. -/
def IsPrimitive {R : Type*} {H : Type*} [CommSemiring R] [Semiring H] [Bialgebra R H]
    (x : H) : Prop :=
  Coalgebra.comul (R := R) x = x ⊗ₜ 1 + 1 ⊗ₜ x

/-- The `R`-submodule of primitive elements of a bialgebra. -/
def primitiveElements {R : Type*} {H : Type*} [CommSemiring R] [Semiring H]
    [Bialgebra R H] : Submodule R H where
  carrier := {x : H | IsPrimitive (R := R) x}
  add_mem' {x y} hx hy := by
    simp only [Set.mem_setOf_eq] at *
    unfold IsPrimitive at *
    rw [map_add, hx, hy, TensorProduct.add_tmul, TensorProduct.tmul_add]
    abel
  zero_mem' := by
    simp only [Set.mem_setOf_eq]
    unfold IsPrimitive
    simp [TensorProduct.zero_tmul, TensorProduct.tmul_zero]
  smul_mem' r x hx := by
    simp only [Set.mem_setOf_eq] at *
    unfold IsPrimitive at *
    rw [LinearMap.map_smul, hx]
    simp [TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_add]

end HopfAlgebra


namespace TensorCategories

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Vanishing of `Ext¹(X, Y)`: every short exact sequence `0 → Y → V → X → 0` in `C` splits. -/
def Ext1Vanishes (X Y : C) : Prop :=
  ∀ (V : C) (f : Y ⟶ V) (g : V ⟶ X) (hfg : f ≫ g = 0),
    (ShortComplex.mk f g hfg).ShortExact → Nonempty (ShortComplex.mk f g hfg).Splitting

end TensorCategories
end
