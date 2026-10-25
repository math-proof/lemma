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
import Theorem.v1.Atlas.TensorCategories.code.K0Bimodule.Part3
set_option maxHeartbeats 800000

open Finset FusionRing


namespace FusionRing

variable {ι : Type*} [DecidableEq ι] [Fintype ι] (R : FusionRing ι)

/-- `K₀(R)` is a right module over the Grothendieck ring `Gr(R)`, presented as a left module
over `Gr(R)ᵐᵒᵖ`. -/
instance instModuleOp : Module (GrRingOf R)ᵐᵒᵖ (K0Group R) where
  one_smul m := by
    ext k
    show R.k0ActRight m.coeff R.grOne k = m.coeff k
    rw [R.k0ActRight_one]
  mul_smul r s m := by
    ext k

    change R.k0ActRight m.coeff (R.grMul s.unop.coeff r.unop.coeff) k =
           R.k0ActRight (R.k0ActRight m.coeff s.unop.coeff) r.unop.coeff k
    rw [← R.k0ActRight_mul_assoc]
  smul_zero r := by
    ext k
    show R.k0ActRight (fun _ => 0) r.unop.coeff k = 0
    rw [R.k0ActRight_zero_left]
  smul_add r m₁ m₂ := by
    ext k
    show R.k0ActRight (fun k => m₁.coeff k + m₂.coeff k) r.unop.coeff k =
         R.k0ActRight m₁.coeff r.unop.coeff k +
           R.k0ActRight m₂.coeff r.unop.coeff k
    rw [R.k0ActRight_add_left]
  add_smul r₁ r₂ m := by
    ext k
    show R.k0ActRight m.coeff (fun k => r₁.unop.coeff k + r₂.unop.coeff k) k =
         R.k0ActRight m.coeff r₁.unop.coeff k +
           R.k0ActRight m.coeff r₂.unop.coeff k
    rw [R.k0ActRight_add_right]
  zero_smul m := by
    ext k
    show R.k0ActRight m.coeff (fun _ => 0) k = 0
    rw [R.k0ActRight_zero_right]

/-- The left and right actions of the Grothendieck ring on `K₀(R)` commute, equipping it
with a `Gr(R)`-bimodule structure. -/
instance instSMulCommClass :
    SMulCommClass (GrRingOf R) (GrRingOf R)ᵐᵒᵖ (K0Group R) where
  smul_comm r s m := by
    ext l
    show R.k0ActLeft r.coeff (R.k0ActRight m.coeff s.unop.coeff) l =
         R.k0ActRight (R.k0ActLeft r.coeff m.coeff) s.unop.coeff l
    rw [R.k0ActLeft_eq_grMul, R.k0ActLeft_eq_grMul]
    exact congr_fun (R.k0_bimodule_compat r.coeff m.coeff s.unop.coeff) l

end FusionRing
