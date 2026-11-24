module
public import Def.v1.Atlas.LieGroups.code.VermaModules.Part7
public import Theorem.Int.WeightSubspace.eq.ToSubmoduleWeightSpace
public import Theorem.Int.IsInQPlus0
public import Def.v1.Atlas.LieGroups.code.CategoryO.Part3
public import Mathlib.Algebra.Lie.TensorProduct
public import Mathlib.Algebra.Lie.Submodule
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Algebra.Lie.Semisimple.Defs
public import Mathlib.RingTheory.Finiteness.Basic
public import Structure.v1.Atlas.LieGroups.code.PrincipalSeries


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/PrincipalSeries.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
noncomputable section

universe u_mod

variable (R : Type*) [CommRing R]

variable (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra R 𝔤]

def IsLocallyFiniteMap
    {M : Type*} [AddCommGroup M] [Module R M]
    {N : Type*} [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) : Prop :=
  (LinearMap.range f).FG

def RestrictedDual
    (M : Type*) [AddCommGroup M] [Module R M] :
    Type _ :=
  { f : Module.Dual R M // ∃ (N : Submodule R M),
      N ≤ LinearMap.ker f ∧ (Submodule.map (Submodule.mkQ N) ⊤).FG }

def IsInRestrictedDual
    {M : Type*} [AddCommGroup M] [Module R M]
    (f : Module.Dual R M) : Prop :=
  ∃ (N : Submodule R M), N ≤ LinearMap.ker f ∧ (Submodule.map (Submodule.mkQ N) ⊤).FG

end
