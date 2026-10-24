/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/BooleanUpDown.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.AlgebraicCombinatorics.code.BooleanCommutator
import Lemma.Finset.Atlas.v1.AlgebraicCombinatorics.code.BooleanCommutator
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

open Finset BigOperators

set_option autoImplicit false

namespace BooleanUpDown

variable {n : ℕ}

abbrev Level (n i : ℕ) := { s : Finset (Fin n) // s.card = i }

def up (i : ℕ) (v : Level n i → ℝ) : Level n (i + 1) → ℝ := fun y =>
  ∑ x : Level n i, if x.val ⊆ y.val then v x else 0

def down (i : ℕ) (w : Level n (i + 1) → ℝ) : Level n i → ℝ := fun x =>
  ∑ y : Level n (i + 1), if x.val ⊆ y.val then w y else 0

def innerProd {α : Type*} [Fintype α] (f g : α → ℝ) : ℝ :=
  ∑ x : α, f x * g x

def DU_form (i : ℕ) (v w : Level n i → ℝ) : ℝ :=
  ∑ x : Level n i, ∑ z : Level n i,
    (BooleanCommutator.DU_coeff i x.val z.val : ℝ) * v x * w z

def UD_form (i : ℕ) (v w : Level n i → ℝ) : ℝ :=
  ∑ x : Level n i, ∑ z : Level n i,
    (BooleanCommutator.UD_coeff i x.val z.val : ℝ) * v x * w z
