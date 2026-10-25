/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/CoxeterTheory.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.LieGroups.code.CategoryO.Part3
import Lemma.Int.IsInQPlus0
import Lemma.Finset.EqMul_Mul.of.In_SimpleReflections
import Def.v1.Atlas.LieGroups.code.HeckeKL.Part9
import Def.v1.Atlas.LieGroups.code.CoxeterTheory


noncomputable section

open scoped BigOperators

structure SimpleRootData
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (C : CoxeterGroupData)
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ)
    (rs : RootSystemWithReflections rd wg)
    (compat : CoxeterWeylCompatibility C rd wg) where
  simpleRoot : C.W → Δ.𝔥 →ₗ[R] R
  simpleRoot_pos : ∀ s ∈ C.simpleReflections, simpleRoot s ∈ rd.posRoots
  simpleRoot_mem : ∀ s ∈ C.simpleReflections, simpleRoot s ∈ rs.allRoots
  simpleRoot_refl : ∀ s ∈ C.simpleReflections, rs.reflection (simpleRoot s) = compat.ι s
  simpleRoot_injective : ∀ s₁ ∈ C.simpleReflections, ∀ s₂ ∈ C.simpleReflections,
    simpleRoot s₁ = simpleRoot s₂ → s₁ = s₂

end
