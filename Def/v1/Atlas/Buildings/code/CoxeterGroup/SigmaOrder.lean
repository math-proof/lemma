/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/SigmaOrder.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.Buildings.code.CoxeterGroup.Basic.Part3
open Finset BigOperators


namespace CoxeterGroup

variable {B : Type*} [DecidableEq B] [Fintype B]

/-- The simple reflection $\sigma_s$ packaged as an $\mathbb{R}$-linear endomorphism of $\mathbb{R}^B$. -/
noncomputable def sigmaLin (M : CoxeterMatrix B) (s : B) : Module.End ℝ (B → ℝ) where
  toFun := sigma M s
  map_add' := by
    intro v w; ext t
    simp only [sigma, bilinForm, Pi.add_apply]
    simp_rw [add_mul, Finset.sum_add_distrib]
    ring
  map_smul' := by
    intro r v; ext t
    simp only [sigma, bilinForm, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    have : (∑ x : B, ∑ x_1 : B, r * v x * formVal M x x_1 * e s x_1) =
        r * (∑ x : B, ∑ x_1 : B, v x * formVal M x x_1 * e s x_1) := by
      rw [Finset.mul_sum]; congr 1; funext x
      rw [Finset.mul_sum]; congr 1; funext x_1; ring
    rw [this]; ring

end CoxeterGroup
