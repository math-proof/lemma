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
import Def.v1.Atlas.LieGroups.code.InfinitesimalEquivalenceCore


noncomputable section

structure GKModule.IsUnitary
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    {K : Type*} [Group K]
    {𝔨 : LieSubalgebra ℂ 𝔤}
    {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]
    (M : GKModule 𝔤 K 𝔨 Ad V) where
  form : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ
  conj_symm : ∀ (v w : V), form w v = starRingEnd ℂ (form v w)
  re_nonneg : ∀ (v : V), 0 ≤ (form v v).re
  definite : ∀ (v : V), form v v = 0 → v = 0
  pos_def : ∀ v : V, v ≠ 0 → 0 < (form v v).re
  K_invariant : ∀ (k : K) (v w : V), form (M.σ k v) (M.σ k w) = form v w
  lie_invariant : ∀ (X : 𝔤) (v w : V), form ⁅X, v⁆ w + form v ⁅X, w⁆ = 0

end
