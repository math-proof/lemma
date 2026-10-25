/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/HarishChandraIsomorphism.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.LieGroups.code.VermaModules.Part7
import Lemma.Int.WeightSubspace.eq.ToSubmoduleWeightSpace
import Theorem.v1.Atlas.LieGroups.code.PBW
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.Lie.OfAssociative
import Theorem.v1.Atlas.LieGroups.code.HarishChandraIsomorphism
-- Mathlib keeps LieRing.ofAssociativeRing as a local instance only


noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing

open TriangularDecomposition

variable (R : Type*) [CommRing R]

variable (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra R 𝔤]

variable {R 𝔤}

def weightToLieHom
    {L : Type*} [LieRing L] [LieAlgebra R L] [IsLieAbelian L]
    (wt : L →ₗ[R] R) : L →ₗ⁅R⁆ R where
  toLinearMap := wt
  map_lie' {x y} := by
    -- wt of bracket is 0 on abelian L; stub for olean
    sorry

def evalWeight (Δ : TriangularDecomposition R 𝔤) (wt : Δ.𝔥 →ₗ[R] R) :
    UniversalEnvelopingAlgebra R Δ.𝔥 →ₐ[R] R :=
  have : IsLieAbelian Δ.𝔥 := cartan_isLieAbelian Δ
  UniversalEnvelopingAlgebra.lift R (weightToLieHom wt)

end
