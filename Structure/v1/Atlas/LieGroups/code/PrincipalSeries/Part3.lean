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
public import Def.v1.Atlas.LieGroups.code.PrincipalSeries.Part2


public noncomputable section

universe u_mod

variable (R : Type*) [CommRing R]

variable (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra R 𝔤]

variable {R 𝔤}

attribute [instance] PrincipalSeriesBimodule.M_source_acg
  PrincipalSeriesBimodule.M_source_mod PrincipalSeriesBimodule.M_source_lrm
  PrincipalSeriesBimodule.M_source_lm PrincipalSeriesBimodule.M_target_acg
  PrincipalSeriesBimodule.M_target_mod PrincipalSeriesBimodule.M_target_lrm
  PrincipalSeriesBimodule.M_target_lm

structure HCBimoduleHom
    {M : Type*} [AddCommGroup M] [Module R M]
    {N : Type*} [AddCommGroup N] [Module R N]
    (hcM : PS_IsHarishChandraBimodule R 𝔤 M)
    (hcN : PS_IsHarishChandraBimodule R 𝔤 N) where
  toLinearMap : M →ₗ[R] N
  left_compat : ∀ (x : 𝔤) (m : M),
    toLinearMap (hcM.left_action x m) = hcN.left_action x (toLinearMap m)
  right_compat : ∀ (x : 𝔤) (m : M),
    toLinearMap (hcM.right_action x m) = hcN.right_action x (toLinearMap m)

end
