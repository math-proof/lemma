/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/PrincipalSeries.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Def.v1.Atlas.LieGroups.code.VermaModules.Part7
public import Lemma.Int.WeightSubspace.eq.ToSubmoduleWeightSpace
public import Lemma.Int.IsInQPlus0
public import Def.v1.Atlas.LieGroups.code.CategoryO.Part3
public import Mathlib.Algebra.Lie.TensorProduct
public import Mathlib.Algebra.Lie.Submodule
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Algebra.Lie.Semisimple.Defs
public import Mathlib.RingTheory.Finiteness.Basic


public noncomputable section

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
