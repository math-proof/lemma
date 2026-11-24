module
public import Def.v1.Atlas.LieGroups.code.GKModule.Part2
public import Theorem.v1.Atlas.LieGroups.code.SL2Basics.Part4
public import Theorem.Nat.basisHC.eq.SMul
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Semisimple
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.Algebra.Lie.OfAssociative
public import Def.v1.Atlas.LieGroups.code.KTypeDecomposition


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/KTypeDecomposition.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

attribute [local instance 100] LieRing.ofAssociativeRing

open Module

-- Mathlib keeps LieRing.ofAssociativeRing as a local instance only


noncomputable section

namespace SL2GKModule

variable {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]

variable {K : Type*} [Group K]

variable {𝔨 : LieSubalgebra ℂ 𝔤}

variable {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
  [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]

omit [LieAlgebra ℂ 𝔤] [Module ℂ V] [LieModule ℂ 𝔤 V] in
@[simp] theorem iterLie_zero (X : 𝔤) (v : V) : iterLie X v 0 = v := rfl

omit [LieAlgebra ℂ 𝔤] [Module ℂ V] [LieModule ℂ 𝔤 V] in
@[simp] theorem iterLie_succ (X : 𝔤) (v : V) (k : ℕ) :
    iterLie X v (k + 1) = ⁅X, iterLie X v k⁆ := rfl

end SL2GKModule
end
