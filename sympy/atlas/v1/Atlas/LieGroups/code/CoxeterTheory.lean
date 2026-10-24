/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/CoxeterTheory.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.LieGroups.code.CategoryO
import Lemma.Int.IsInQPlus0
import Lemma.Finset.EqMul_Mul.of.In_SimpleReflections
import sympy.atlas.v1.Atlas.LieGroups.code.HeckeKL

noncomputable section

open scoped BigOperators

namespace CoxeterGroupData

variable (C : CoxeterGroupData)

structure ReducedWord (w : C.W) where
  word : List C.W
  mem_simple : ∀ s ∈ word, s ∈ C.simpleReflections
  prod_eq : word.prod = w
  length_eq : word.length = C.length w

def IsReducedWord (word : List C.W) : Prop :=
  (∀ s ∈ word, s ∈ C.simpleReflections) ∧ word.length = C.length word.prod

def weylLength (wg : WeylGroupData Δ) (C : CoxeterGroupData)
    (rd : PositiveRootData Δ) (compat : CoxeterWeylCompatibility C rd wg)
    (w : wg.W) : ℕ :=
  C.length (compat.ι.symm w)

end WeylGroupData

namespace RootSystemWithReflections

variable {R : Type*} [CommRing R]
variable {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
variable {Δ : TriangularDecomposition R 𝔤}
variable {rd : PositiveRootData Δ}
variable {wg : WeylGroupData Δ}

def inversions (_rs : RootSystemWithReflections rd wg)
    (w : wg.W) : Finset (Δ.𝔥 →ₗ[R] R) := by
  classical
  exact rd.posRoots.filter (fun α => -(wg.dualAction w α) ∈ rd.posRoots)

end RootSystemWithReflections

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
