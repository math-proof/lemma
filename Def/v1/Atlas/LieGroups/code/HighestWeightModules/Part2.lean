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
import Structure.v1.Atlas.LieGroups.code.HighestWeightModules


noncomputable section

universe u_mod

variable (R : Type*) [CommRing R]

variable (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra R 𝔤]

variable {R 𝔤}

def ChevalleyData.IsDominantIntegral
    {Δ : TriangularDecomposition R 𝔤}
    (chev : ChevalleyData Δ) (wt : Δ.𝔥 →ₗ[R] R) : Prop :=
  ∀ (i : Fin chev.rank), ∃ (n : ℕ), wt (chev.simpleCoroot i) = (n : R)

def ChevalleyData.IsInWeightLattice
    {Δ : TriangularDecomposition R 𝔤}
    (chev : ChevalleyData Δ) (wt : Δ.𝔥 →ₗ[R] R) : Prop :=
  ∀ (i : Fin chev.rank), ∃ (n : ℤ), wt (chev.simpleCoroot i) = (n : R)

end
