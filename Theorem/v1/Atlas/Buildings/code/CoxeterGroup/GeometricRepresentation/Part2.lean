/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/GeometricRepresentation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.Buildings.code.CoxeterGroup.Basic.Part3
import Def.v1.Atlas.Buildings.code.CoxeterGroup.GeometricRepresentation
open Finset BigOperators


namespace CoxeterGroup

variable {B : Type*} [DecidableEq B] [Fintype B]


/-- Sign flip on the simple root: $\langle \sigma_s v, \alpha_s \rangle = -\langle v, \alpha_s\rangle$. -/
theorem bilinForm_sigma_e (M : CoxeterMatrix B) (s : B) (v : B → ℝ) :
    bilinForm M (sigma M s v) (e s) = -(bilinForm M v (e s)) := by

  have sigma_eq : sigma M s v = v + (-2 * bilinForm M v (e s)) • e s := by
    ext t; simp only [sigma, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  rw [sigma_eq, bilinForm_add_left, bilinForm_smul_left, bilinForm_e_e, formVal_diag]
  ring

/-- Involution: $\sigma_s \circ \sigma_s = \mathrm{id}$ on $\mathbb{R}^B$. -/
theorem sigma_involution (M : CoxeterMatrix B) (s : B) (v : B → ℝ) :
    sigma M s (sigma M s v) = v := by
  ext t
  simp only [sigma]
  rw [bilinForm_sigma_e]
  ring

end CoxeterGroup
