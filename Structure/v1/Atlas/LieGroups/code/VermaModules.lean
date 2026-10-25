/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/VermaModules.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Lie.Subalgebra
import Mathlib.Algebra.Lie.Submodule
import Mathlib.Algebra.Lie.Quotient
import Mathlib.Algebra.Lie.UniversalEnveloping
import Mathlib.Algebra.Lie.Weights.Basic
import Mathlib.Algebra.Lie.Semisimple.Basic
import Mathlib.Algebra.Lie.CartanSubalgebra
import Mathlib.Order.Atoms
import Mathlib.RingTheory.Congruence.Defs


noncomputable section

universe u_mod

variable (R : Type*) [CommRing R]

variable (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra R 𝔤]

structure TriangularDecomposition where
  𝔥 : LieSubalgebra R 𝔤
  𝔫_pos : LieSubalgebra R 𝔤
  𝔫_neg : LieSubalgebra R 𝔤
  is_cartan : 𝔥.IsCartanSubalgebra
  h_abelian : IsLieAbelian 𝔥
  decomp_exists : ∀ x : 𝔤, ∃ (n_neg : 𝔫_neg) (h : 𝔥) (n_pos : 𝔫_pos),
    x = (n_neg : 𝔤) + (h : 𝔤) + (n_pos : 𝔤)
  decomp_unique : ∀ (n₁ n₁' : 𝔫_neg) (h₁ h₁' : 𝔥) (p₁ p₁' : 𝔫_pos),
    (n₁ : 𝔤) + (h₁ : 𝔤) + (p₁ : 𝔤) = (n₁' : 𝔤) + (h₁' : 𝔤) + (p₁' : 𝔤) →
    n₁ = n₁' ∧ h₁ = h₁' ∧ p₁ = p₁'

end
