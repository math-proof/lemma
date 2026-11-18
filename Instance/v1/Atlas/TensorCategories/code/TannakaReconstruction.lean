/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/TannakaReconstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Tannaka
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.CategoryTheory.Monoidal.Functor
public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.Bialgebra.Basic
public import Mathlib.RingTheory.Coalgebra.Basic
public import Mathlib.Algebra.Category.FGModuleCat.Basic
public import Abbrev.v1.Atlas.TensorCategories.code.QuasiBialgebra
public import Abbrev.v1.Atlas.TensorCategories.code.QuasiTensorFunctor.Part5
public import Theorem.Category.Atlas.v1.TensorCategories.code.QuasiTensorFunctor
public import Def.v1.Atlas.TensorCategories.code.TannakaReconstruction

@[expose] public section

set_option maxHeartbeats 800000

open CategoryTheory

universe u v w


noncomputable section

variable (k : Type u) [CommRing k] (A : Type u) [Ring A] [Algebra k A]

theorem endForget₂_algebraMap_comm (r : k) (x : EndForget₂ A) :
    endForget₂AlgebraMap k A r * x = x * endForget₂AlgebraMap k A r := by
  unfold endForget₂AlgebraMap
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
  set a := (ringEquivEndForget₂ A).symm x
  have hx : x = ringEquivEndForget₂ A a := (ringEquivEndForget₂ A).apply_symm_apply x ▸ rfl
  rw [hx, ← map_mul, ← map_mul, Algebra.commutes]

/-- The `k`-algebra structure on `EndForget₂ A` induced by the central ring homomorphism
`endForget₂AlgebraMap`. -/
instance endForget₂Algebra : Algebra k (EndForget₂ A) :=
  (endForget₂AlgebraMap k A).toAlgebra' (endForget₂_algebraMap_comm k A)

end
