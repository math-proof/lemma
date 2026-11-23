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
public import Instance.v1.Atlas.TensorCategories.code.SkewPrimitiveCategorical

@[expose] public section

set_option maxHeartbeats 800000

open Coalgebra
open scoped TensorProduct
open CategoryTheory MonoidalCategory Category Limits

universe v u w


noncomputable section

section ComoduleExt

variable {k : Type u} {C : Type u} [Field k] [AddCommGroup C] [Module k C] [Coalgebra k C]

/-- The space `Ext¹` of comodule extensions between grouplikes `g` and `h`, defined as
equivalence classes of comodule extensions. -/
def ComoduleExt1 (g h : C) : Type u :=
  Quotient (ComoduleExtension.setoid (k := k) g h)

/-- Form the `Ext¹` equivalence class of a comodule extension. -/
def ComoduleExt1.mk {g h : C} (E : ComoduleExtension (k := k) g h) :
    ComoduleExt1 (k := k) g h :=
  Quotient.mk _ E

end ComoduleExt
end
