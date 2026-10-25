/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/PrincipalSeries.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.LieGroups.code.VermaModules.Part7
import Lemma.Int.WeightSubspace.eq.ToSubmoduleWeightSpace
import Lemma.Int.IsInQPlus0
import Def.v1.Atlas.LieGroups.code.CategoryO.Part3
import Mathlib.Algebra.Lie.TensorProduct
import Mathlib.Algebra.Lie.Submodule
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Algebra.Lie.Semisimple.Defs
import Mathlib.RingTheory.Finiteness.Basic


noncomputable section

universe u_mod

variable (R : Type*) [CommRing R]

variable (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra R 𝔤]

structure PS_IsHarishChandraBimodule
    (M : Type*) [AddCommGroup M] [Module R M] where
  left_action : 𝔤 →ₗ⁅R⁆ Module.End R M
  right_action : 𝔤 →ₗ⁅R⁆ Module.End R M
  actions_comm : ∀ (x y : 𝔤) (m : M),
    left_action x (right_action y m) = right_action y (left_action x m)
  locally_finite_diag : ∀ m : M,
    (Submodule.span R (Set.range (fun x => left_action x m - right_action x m))).FG

end
