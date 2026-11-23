/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/VermaModules.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Lie.Basic
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.Lie.Subalgebra
public import Mathlib.Algebra.Lie.Submodule
public import Mathlib.Algebra.Lie.Quotient
public import Mathlib.Algebra.Lie.UniversalEnveloping
public import Mathlib.Algebra.Lie.Weights.Basic
public import Mathlib.Algebra.Lie.Semisimple.Basic
public import Mathlib.Algebra.Lie.CartanSubalgebra
public import Mathlib.Order.Atoms
public import Mathlib.RingTheory.Congruence.Defs
public import Instance.v1.Atlas.LieGroups.code.VermaModules

@[expose] public section

noncomputable section

universe u_mod

variable (R : Type*) [CommRing R]

variable (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra R 𝔤]

variable {R 𝔤}

namespace TriangularDecomposition

variable (Δ : TriangularDecomposition R 𝔤)

def VermaModule.highestWeightVec (Δ : TriangularDecomposition R 𝔤) (wt : Δ.𝔥 →ₗ[R] R) :
    VermaModule Δ wt :=
  (vermaIdeal Δ wt).toQuotient 1

end TriangularDecomposition
end
