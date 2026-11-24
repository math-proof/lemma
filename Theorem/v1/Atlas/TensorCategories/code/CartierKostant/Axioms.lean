module
public import Theorem.v1.Atlas.TensorCategories.code.HopfAlgebra.Part3
public import Theorem.Category.Atlas.v1.TensorCategories.code.HopfAlgebra
public import Theorem.Category.Atlas.v1.TensorCategories.code.CoradicalFiltration
public import Def.v1.Atlas.TensorCategories.code.CoradicalFiltration.Part8
public import Mathlib.Algebra.Lie.UniversalEnveloping
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.LinearAlgebra.TensorAlgebra.Basic
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
public import Mathlib.RingTheory.Nilpotent.GeometricallyReduced
public import Mathlib.RingTheory.HopfAlgebra.TensorProduct
public import Mathlib.RingTheory.Coalgebra.Hom
public import Mathlib.RingTheory.Smooth.Basic
public import Def.v1.Atlas.TensorCategories.code.CartierKostant.Axioms
set_option maxHeartbeats 800000
open Coalgebra HopfAlgebra
open scoped TensorProduct


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/CartierKostant/Axioms.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
universe u v


/-- The Lie bracket of two primitive elements is primitive, so primitive elements form a
Lie subalgebra. -/
theorem HopfAlgebra.IsPrimitive.lie_bracket {x y : H}
    (hx : HopfAlgebra.IsPrimitive (R := R) x)
    (hy : HopfAlgebra.IsPrimitive (R := R) y) :
    HopfAlgebra.IsPrimitive (R := R) ⁅x, y⁆ := by
  rw [Ring.lie_def]
  unfold HopfAlgebra.IsPrimitive at *
  rw [map_sub, Bialgebra.comul_mul, Bialgebra.comul_mul, hx, hy]
  simp only [mul_add, add_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul,
    TensorProduct.sub_tmul, TensorProduct.tmul_sub]
  abel

