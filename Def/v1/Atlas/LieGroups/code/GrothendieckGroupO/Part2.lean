module
public import Def.v1.Atlas.LieGroups.code.ProjectiveFunctors.Part7
public import Theorem.Int.IsDirectSummand
public import Theorem.Finset.EqMul_Mul.of.In_SimpleReflections
public import Def.v1.Atlas.LieGroups.code.HeckeKL.Part9
public import Theorem.v1.Atlas.LieGroups.code.GrothendieckGroupO
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/GrothendieckGroupO.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
noncomputable section

open scoped TensorProduct

open ProjectiveFunctors Classical

universe u

variable {R : Type u} [CommRing R]

variable {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]

def DominatesSet
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (lam : Δ.𝔥 →ₗ[R] R)
    (S : Set (Δ.𝔥 →ₗ[R] R)) : Prop :=
  ∀ mu ∈ S, rd.IsInQPlus (lam - mu)

end
