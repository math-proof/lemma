/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/SkewPrimitiveCategorical.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Category.FGModuleCat.Basic
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.CategoryTheory.Simple
public import Mathlib.CategoryTheory.Monoidal.Category
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.Spectrum.Maximal.Basic
public import Abbrev.v1.Atlas.TensorCategories.code.SkewPrimitiveCategorical

@[expose] public section

set_option maxHeartbeats 800000

open Coalgebra
open scoped TensorProduct
open CategoryTheory MonoidalCategory Category Limits

universe v u w


noncomputable section

section ComoduleExt

variable {k : Type u} {C : Type u} [Field k] [AddCommGroup C] [Module k C] [Coalgebra k C]

def ext1ToSkewQuot {g h : C} :
    ComoduleExt1 (k := k) g h → SkewQuot (k := k) g h :=
  Quotient.lift
    (fun E => Submodule.Quotient.mk (p := Submodule.comap
      (skewPrimitiveSpace (R := k) g h).subtype
      (trivialSkewPrimitiveSubspace (k := k) g h))
      ⟨E.x, E.skew_prim⟩)
    (by
      intro E₁ E₂ (hE : ComoduleExtension.Equiv E₁ E₂)
      rw [Submodule.Quotient.eq]
      rw [Submodule.mem_comap]
      simp only [Submodule.subtype_apply, Submodule.coe_sub]
      exact hE)

def skewQuotToExt1 {g h : C} :
    SkewQuot (k := k) g h → ComoduleExt1 (k := k) g h :=
  Quotient.lift
    (fun (p : skewPrimitiveSpace (R := k) g h) =>
      ComoduleExt1.mk (k := k) (ComoduleExtension.ofSkewPrimitive (k := k) p))
    (by
      intro a b hab
      apply Quotient.sound
      show ComoduleExtension.Equiv _ _
      unfold ComoduleExtension.Equiv ComoduleExtension.ofSkewPrimitive
      simp only
      have hab' : a - b ∈ Submodule.comap (skewPrimitiveSpace (R := k) g h).subtype
          (trivialSkewPrimitiveSubspace (k := k) g h) := by
        exact (Submodule.quotientRel_def _).mp hab
      rw [Submodule.mem_comap] at hab'
      simp only [Submodule.subtype_apply, Submodule.coe_sub] at hab'
      exact hab')

/-- The canonical bijection between `Ext¹(k·h, k·g)` and the reduced skew-primitive quotient
`skewPrimitiveSpace g h / trivialSkewPrimitiveSubspace g h`. -/
def ext1EquivSkewQuot {g h : C} :
    ComoduleExt1 (k := k) g h ≃ SkewQuot (k := k) g h where
  toFun := ext1ToSkewQuot
  invFun := skewQuotToExt1
  left_inv := by
    intro q
    induction q using Quotient.inductionOn with
    | h E =>
      simp only [ext1ToSkewQuot, skewQuotToExt1, ComoduleExt1.mk,
        ComoduleExtension.ofSkewPrimitive]
      rfl
  right_inv := by
    intro q
    induction q using Quotient.inductionOn with
    | h p =>
      simp only [ext1ToSkewQuot, skewQuotToExt1, ComoduleExt1.mk,
        ComoduleExtension.ofSkewPrimitive]
      rfl

end ComoduleExt
end
