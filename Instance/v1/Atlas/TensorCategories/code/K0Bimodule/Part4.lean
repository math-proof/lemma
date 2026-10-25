/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/K0Bimodule.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.TensorCategories.code.GrothendieckRing.Part2
import Lemma.Category.Atlas.v1.TensorCategories.code.GrothendieckRing
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Group.Opposite
import Theorem.v1.Atlas.TensorCategories.code.K0Bimodule.Part2
set_option maxHeartbeats 800000

open Finset FusionRing


namespace FusionRing

variable {ι : Type*} [DecidableEq ι] [Fintype ι] (R : FusionRing ι)

/-- `K₀(R)` is a left module over the Grothendieck ring `Gr(R)`. -/
instance instModule : Module (GrRingOf R) (K0Group R) where
  one_smul m := by
    ext k
    show R.k0ActLeft R.grOne m.coeff k = m.coeff k
    rw [R.k0ActLeft_eq_grMul, R.grMul_one_left]
  mul_smul r s m := by
    ext k
    show R.k0ActLeft (R.grMul r.coeff s.coeff) m.coeff k =
         R.k0ActLeft r.coeff (R.k0ActLeft s.coeff m.coeff) k
    simp only [R.k0ActLeft_eq_grMul]
    rw [R.grMul_assoc]
  smul_zero r := by
    ext k
    show R.k0ActLeft r.coeff (fun _ => 0) k = 0
    rw [R.k0ActLeft_eq_grMul, R.grMul_zero]
  smul_add r m₁ m₂ := by
    ext k
    show R.k0ActLeft r.coeff (fun k => m₁.coeff k + m₂.coeff k) k =
         R.k0ActLeft r.coeff m₁.coeff k + R.k0ActLeft r.coeff m₂.coeff k
    simp only [R.k0ActLeft_eq_grMul]
    rw [R.grMul_left_distrib]
  add_smul r₁ r₂ m := by
    ext k
    show R.k0ActLeft (fun k => r₁.coeff k + r₂.coeff k) m.coeff k =
         R.k0ActLeft r₁.coeff m.coeff k + R.k0ActLeft r₂.coeff m.coeff k
    simp only [R.k0ActLeft_eq_grMul]
    rw [R.grMul_right_distrib]
  zero_smul m := by
    ext k
    show R.k0ActLeft (fun _ => 0) m.coeff k = 0
    rw [R.k0ActLeft_eq_grMul, R.grZero_mul]

/-- Right action of `Gr(R)ᵐᵒᵖ` on `K₀(R)` via `k0ActRight`. -/
instance instSMulRight : SMul (GrRingOf R)ᵐᵒᵖ (K0Group R) :=
  ⟨fun r m => ⟨R.k0ActRight m.coeff r.unop.coeff⟩⟩

end FusionRing
