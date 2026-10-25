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
import Def.v1.Atlas.TensorCategories.code.CartierKostant.Axioms
set_option maxHeartbeats 800000

open Coalgebra HopfAlgebra
open scoped TensorProduct

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

