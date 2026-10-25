/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/CartierKostant/Axioms.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.TensorCategories.code.HopfAlgebra.Part3
import Lemma.Category.Atlas.v1.TensorCategories.code.HopfAlgebra
import Lemma.Category.Atlas.v1.TensorCategories.code.CoradicalFiltration
import Def.v1.Atlas.TensorCategories.code.CoradicalFiltration.Part8
import Mathlib.Algebra.Lie.UniversalEnveloping
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.LinearAlgebra.TensorAlgebra.Basic
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
import Mathlib.RingTheory.Nilpotent.GeometricallyReduced
import Mathlib.RingTheory.HopfAlgebra.TensorProduct
import Mathlib.RingTheory.Coalgebra.Hom
import Mathlib.RingTheory.Smooth.Basic
import Class.v1.Atlas.TensorCategories.code.CartierKostant.Axioms
set_option maxHeartbeats 800000

open Coalgebra HopfAlgebra
open scoped TensorProduct

universe u v


/-- An element `x` of a bialgebra `H` is primitive if `Δ x = x ⊗ 1 + 1 ⊗ x`. -/
def HopfAlgebra.IsPrimitive (x : H) : Prop :=
  Coalgebra.comul (R := R) x = x ⊗ₜ 1 + 1 ⊗ₜ x

/-- The submodule of primitive elements of a bialgebra `H` over `R`. -/
def HopfAlgebra.primitiveElements : Submodule R H where
  carrier := {x : H | HopfAlgebra.IsPrimitive (R := R) x}
  add_mem' {x y} (hx : HopfAlgebra.IsPrimitive x) (hy : HopfAlgebra.IsPrimitive y) := by
    show HopfAlgebra.IsPrimitive (R := R) (x + y)
    unfold HopfAlgebra.IsPrimitive at *
    rw [map_add, hx, hy, TensorProduct.add_tmul, TensorProduct.tmul_add]
    abel
  zero_mem' := by
    show HopfAlgebra.IsPrimitive (R := R) 0
    simp [HopfAlgebra.IsPrimitive, TensorProduct.zero_tmul, TensorProduct.tmul_zero]
  smul_mem' r x (hx : HopfAlgebra.IsPrimitive x) := by
    show HopfAlgebra.IsPrimitive (R := R) (r • x)
    unfold HopfAlgebra.IsPrimitive at *
    rw [LinearMap.map_smul, hx]
    simp [TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_add]

