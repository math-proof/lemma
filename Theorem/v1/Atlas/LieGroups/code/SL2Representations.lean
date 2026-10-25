/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/SL2Representations.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.LieGroups.code.SL2Basics.Part4
import Lemma.Nat.basisHC.eq.SMul
import Lemma.Complex.In_WeightSpace.is.H.eq.SMul
import Def.v1.Atlas.LieGroups.code.GKModule.Part2
import Def.v1.Atlas.LieGroups.code.KTypeDecomposition.Part3
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Lie.OfAssociative
import Def.v1.Atlas.LieGroups.code.SL2Representations
attribute [local instance 100] LieRing.ofAssociativeRing

-- Mathlib keeps LieRing.ofAssociativeRing as a local instance only


noncomputable section

open Complex Module

theorem GKModule.IsIsomorphicGK.symm
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    {K : Type*} [Group K]
    {𝔨 : LieSubalgebra ℂ 𝔤}
    {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]
    {W : Type*} [AddCommGroup W] [Module ℂ W]
    [LieRingModule 𝔤 W] [LieModule ℂ 𝔤 W]
    {M : GKModule 𝔤 K 𝔨 Ad V} {N : GKModule 𝔤 K 𝔨 Ad W}
    (h : M.IsIsomorphicGK N) : N.IsIsomorphicGK M := by
  obtain ⟨φ, hφ⟩ := h
  let e := LinearEquiv.ofBijective φ.toLinearMap hφ
  refine ⟨⟨e.symm.toLinearMap, fun X w => ?_, fun k w => ?_⟩, e.symm.bijective⟩
  ·
    apply e.injective


    show e (e.symm ⁅X, w⁆) = e ⁅X, e.symm w⁆
    rw [e.apply_symm_apply]

    conv_rhs => rw [show (e : V → W) = φ.toLinearMap from
      funext (fun v => LinearEquiv.ofBijective_apply φ.toLinearMap v)]
    rw [φ.lie_comm]
    congr 1
    exact (LinearEquiv.apply_ofBijective_symm_apply φ.toLinearMap w).symm
  ·
    apply e.injective
    show e (e.symm (N.σ k w)) = e (M.σ k (e.symm w))
    rw [e.apply_symm_apply]
    conv_rhs => rw [show (e : V → W) = φ.toLinearMap from
      funext (fun v => LinearEquiv.ofBijective_apply φ.toLinearMap v)]
    rw [φ.group_comm]
    congr 1
    exact (LinearEquiv.apply_ofBijective_symm_apply φ.toLinearMap w).symm

end
