/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/HighestWeightModules.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.LieGroups.code.VermaModules.Part7
import Lemma.Int.WeightSubspace.eq.ToSubmoduleWeightSpace
import Mathlib.Algebra.Lie.Sl2


noncomputable section

universe u_mod

variable (R : Type*) [CommRing R]

variable (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra R 𝔤]

variable {R 𝔤}

def IsSingularVector
    (Δ : TriangularDecomposition R 𝔤)
    {M : Type u_mod} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (wt : Δ.𝔥 →ₗ[R] R) (v : M) : Prop :=
  (∀ (h : Δ.𝔥), ⁅(h : 𝔤), v⁆ = wt h • v) ∧
  (∀ (e : Δ.𝔫_pos), ⁅(e : 𝔤), v⁆ = 0)

end
