/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/GKModuleDefs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.LieGroups.code.GKModule.Part2
import Def.v1.Atlas.LieGroups.code.Admissible.Part3
import Lemma.Bijective.EqContinuousLinearEquivOfBijective.of.Bijective
import Mathlib.Algebra.Lie.Semisimple.Defs
import Instance.v1.Atlas.LieGroups.code.GKModuleDefs


noncomputable section

open scoped ComplexOrder

def IsMaximalCompactSubgroup
    {G : Type*} [Group G] [TopologicalSpace G]
    (K : Subgroup G) [TopologicalSpace K]
    [CompactSpace K] : Prop :=
  ∀ (H : Subgroup G) [TopologicalSpace H] [CompactSpace H],
    ∃ (g : G), ∀ h : G, h ∈ H → g * h * g⁻¹ ∈ K

def GKModule.IsFiniteLength
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    {K : Type*} [Group K]
    {𝔨 : LieSubalgebra ℂ 𝔤}
    {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]
    (M : GKModule 𝔤 K 𝔨 Ad V) : Prop :=
  ∃ n : ℕ, ∃ (chain : Fin (n + 1) → Submodule ℂ V),
    chain ⟨0, Nat.zero_lt_succ n⟩ = ⊥ ∧
    chain ⟨n, Nat.lt_succ_iff.mpr le_rfl⟩ = ⊤ ∧
    (∀ i : Fin n,
      chain ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ <
        chain ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩) ∧
    (∀ i : Fin n,
      M.IsSubmodule (chain ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)) ∧
    (∀ i : Fin n,
      M.IsSubmodule (chain ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)) ∧


    (∀ i : Fin n, ∀ (W : Submodule ℂ V), M.IsSubmodule W →
      chain ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ ≤ W →
      W ≤ chain ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ →
      W = chain ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ ∨
      W = chain ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)

end
