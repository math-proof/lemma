/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/SelbergExpansion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Instance.v1.Atlas.ProjectionTheory.code.SelbergExpansion
open Matrix Finset BigOperators


noncomputable section

namespace SelbergExpansion

section GeneralGroup

variable {G : Type*} [Fintype G] [DecidableEq G] [Group G]

/-- The set of integer `2 × 2` unimodular matrices `g ∈ SL₂(ℤ)` of "size" at most
`T`, i.e. with Frobenius squared norm `g₀₀² + g₀₁² + g₁₀² + g₁₁² ≤ ⌊T²⌋`. -/
def sl2ZBall (T : ℝ) : Set (SpecialLinearGroup (Fin 2) ℤ) :=
  {g | ((((g : Matrix (Fin 2) (Fin 2) ℤ) 0 0) ^ 2 +
         ((g : Matrix (Fin 2) (Fin 2) ℤ) 0 1) ^ 2 +
         ((g : Matrix (Fin 2) (Fin 2) ℤ) 1 0) ^ 2 +
         ((g : Matrix (Fin 2) (Fin 2) ℤ) 1 1) ^ 2 : ℤ) ≤ ⌊T ^ 2⌋)}

/-- The principal congruence subgroup `Γ(p) ⊆ SL₂(ℤ)`: matrices congruent to the
identity modulo `p`. -/
def congruenceSubgroup (p : ℕ) : Set (SpecialLinearGroup (Fin 2) ℤ) :=
  {g | ∀ i j : Fin 2,
    ((g : Matrix (Fin 2) (Fin 2) ℤ) i j - (1 : Matrix (Fin 2) (Fin 2) ℤ) i j) % (p : ℤ) = 0}

end GeneralGroup
end SelbergExpansion
end
