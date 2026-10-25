/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/InfinitesimalEquivalenceCore.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.LieGroups.code.GKModule.Part2
import Def.v1.Atlas.LieGroups.code.GKModuleDefs.Part2
import Structure.v1.Atlas.LieGroups.code.HarishChandraFunctor
import Lemma.Bijective.EqContinuousLinearEquivOfBijective.of.Bijective
import Def.v1.Atlas.LieGroups.code.Admissible.Part3
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.Normed.Module.Completion
import Structure.v1.Atlas.LieGroups.code.InfinitesimalEquivalenceCore.Part2


noncomputable section

def GKModule.IsUnitary.mk'
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    {K : Type*} [Group K]
    {𝔨 : LieSubalgebra ℂ 𝔤}
    {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]
    (M : GKModule 𝔤 K 𝔨 Ad V)
    (form : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ)
    (conj_symm : ∀ (v w : V), form w v = starRingEnd ℂ (form v w))
    (pos_def : ∀ v : V, v ≠ 0 → 0 < (form v v).re)
    (K_invariant : ∀ (k : K) (v w : V), form (M.σ k v) (M.σ k w) = form v w)
    (lie_invariant : ∀ (X : 𝔤) (v w : V), form ⁅X, v⁆ w + form v ⁅X, w⁆ = 0) :
    M.IsUnitary where
  form := form
  conj_symm := conj_symm
  re_nonneg := fun v => by
    by_cases hv : v = 0
    · subst hv; simp [map_zero, LinearMap.map_zero]
    · exact le_of_lt (pos_def v hv)
  definite := fun v hfv => by
    by_contra hv
    have h := pos_def v hv
    rw [hfv, Complex.zero_re] at h
    exact lt_irrefl 0 h
  pos_def := pos_def
  K_invariant := K_invariant
  lie_invariant := lie_invariant

noncomputable def GKModule.IsUnitary.toInnerProductSpaceCore
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    {K : Type*} [Group K]
    {𝔨 : LieSubalgebra ℂ 𝔤}
    {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]
    {M : GKModule 𝔤 K 𝔨 Ad V}
    (hu : M.IsUnitary) : InnerProductSpace.Core ℂ V where
  inner v w := hu.form v w
  conj_inner_symm x y := (hu.conj_symm y x).symm
  re_inner_nonneg x := hu.re_nonneg x
  add_left x y z := by simp [map_add, LinearMap.add_apply]
  smul_left x y r := by simp [LinearMapClass.map_smul]
  definite x hx := hu.definite x (by exact_mod_cast hx)

end
