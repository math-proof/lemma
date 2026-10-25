/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Corollary_1_51_5.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Dimension.Finrank
import Class.v1.Atlas.TensorCategories.code.Corollary_1_51_5
open scoped TensorProduct

universe u₁ u₂


namespace CategoryTheory

/-- Placeholder for the `k`-dimension of the socle of a finite-dimensional `H`-module `M`. -/
def IsIndecomposableModule (H : Type u₂) [Ring H]
    (M : Type u₂) [AddCommGroup M] [Module H M] : Prop :=
  ∀ (N₁ N₂ : Submodule H M), N₁ ⊔ N₂ = ⊤ → N₁ ⊓ N₂ = ⊥ → N₁ = ⊥ ∨ N₂ = ⊥

/-- An `H`-module `M` is projective if every `H`-linear map from `M` to a quotient of
another `H`-module lifts along the quotient map. -/
def IsProjectiveModule (H : Type u₂) [Ring H]
    (M : Type u₂) [AddCommGroup M] [Module H M] : Prop :=
  ∀ {A B : Type u₂} [AddCommGroup A] [AddCommGroup B] [Module H A] [Module H B]
    (f : M →ₗ[H] B) (g : A →ₗ[H] B),
    Function.Surjective g → ∃ h : M →ₗ[H] A, g.comp h = f

/-- A finite-dimensional `k`-algebra `H` is quasi-Frobenius if every projective `H`-module
is also injective, expressed via the standard extension property along injective maps. -/
def IsQuasiFrobeniusAlgebra (k : Type u₁) [Field k]
    (H : Type u₂) [Ring H] [Algebra k H] [Module.Finite k H] : Prop :=
  ∀ (M : Type u₂) [AddCommGroup M] [Module k M] [Module H M] [Module.Finite k M],
    IsProjectiveModule H M →

    ∀ {A B : Type u₂} [AddCommGroup A] [AddCommGroup B] [Module k A] [Module k B]
      [Module H A] [Module H B] (f : M →ₗ[H] B) (g : A →ₗ[H] B),
      Function.Injective g → ∃ h : M →ₗ[H] A, g.comp h = f

end CategoryTheory
