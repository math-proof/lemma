/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/QuantumSl2.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Coalgebra.TensorProduct
set_option maxHeartbeats 400000

open Coalgebra HopfAlgebra
open scoped TensorProduct

universe u v


section Def_1_24_2

variable (R : Type*) [CommRing R] (H : Type*) [Ring H] [Bialgebra R H]

/-- An element `x` of a bialgebra `H` is primitive if `Δ(x) = x ⊗ 1 + 1 ⊗ x`
(Definition 1.24.2 of Etingof–Gelaki–Nikshych–Ostrik). -/
def IsPrimitiveElement (x : H) : Prop :=
  Coalgebra.comul (R := R) x = x ⊗ₜ[R] 1 + 1 ⊗ₜ[R] x

/-- The submodule `Prim(H)` of primitive elements of a bialgebra `H`. -/
def primitiveElements : Submodule R H where
  carrier := {x : H | IsPrimitiveElement R H x}
  add_mem' {x y} (hx : IsPrimitiveElement R H x) (hy : IsPrimitiveElement R H y) := by
    show IsPrimitiveElement R H (x + y)
    unfold IsPrimitiveElement at *
    rw [map_add, hx, hy, TensorProduct.add_tmul, TensorProduct.tmul_add]
    abel
  zero_mem' := by
    show IsPrimitiveElement R H 0
    simp [IsPrimitiveElement, TensorProduct.zero_tmul, TensorProduct.tmul_zero]
  smul_mem' r x (hx : IsPrimitiveElement R H x) := by
    show IsPrimitiveElement R H (r • x)
    unfold IsPrimitiveElement at *
    rw [LinearMap.map_smul, hx]
    simp [TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_add]

end Def_1_24_2
