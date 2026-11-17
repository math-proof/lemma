/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/SchurLemma.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Def.v1.Atlas.LieGroups.code.ContinuousRep.Part3
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Analysis.Normed.Algebra.GelfandFormula
public import Structure.v1.Atlas.LieGroups.code.SchurLemma

@[expose] public section

noncomputable section

open scoped ComplexOrder

namespace FinDimRep

variable {G : Type*} [Group G]

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

def IsIrreducible (π : FinDimRep G V) : Prop :=
  ∀ (W : Submodule ℂ V), (∀ g : G, ∀ v ∈ W, π.toMonoidHom g v ∈ W) → W = ⊥ ∨ W = ⊤

end FinDimRep
end
