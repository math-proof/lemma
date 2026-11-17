/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec4Grassmannian.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.LinearAlgebra.Dimension.Finrank

@[expose] public section

open ExteriorAlgebra


namespace Lec4Grassmannian

section GrassmannianDef

variable (K : Type*) [Field K] (V : Type*) [AddCommGroup V] [Module K V]

/-- Lecture 4: the Grassmannian `Gr(k, V)` of `k`-dimensional subspaces of `V`. -/
def Gr (k : ℕ) := {W : Submodule K V // Module.finrank K W = k}

end GrassmannianDef

section PluckerEmbedding

variable (K : Type*) [Field K] (V : Type*) [AddCommGroup V] [Module K V]
  [Module.Free K V] [Module.Finite K V]

/-- A 2-vector `ω ∈ ⋀^2 M` is *decomposable* if it can be written as a single wedge `v₁ ∧ v₂`. -/
def IsDecomposableTwo (ω : ExteriorAlgebra R M) : Prop :=
  ∃ v₁ v₂ : M, ω = ι R v₁ * ι R v₂

end PluckerEmbedding
end Lec4Grassmannian
