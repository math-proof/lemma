/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/TitsCone.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.Buildings.code.CoxeterGroup.Basic.Part3
import Mathlib.Data.Fintype.BigOperators
import Class.v1.Atlas.Buildings.code.AffineCoxeter.TitsCone
set_option linter.unusedSectionVars false

open Finset BigOperators CoxeterGroup


namespace CoxeterGroup

variable {B : Type*} [DecidableEq B] [Fintype B]

/-- Restriction of a Coxeter matrix $M$ to the parabolic subset $I \subseteq B$ of generators. -/
def CoxeterMatrix.restrict (M : CoxeterMatrix B) (I : Finset B) : CoxeterMatrix ↥I where
  M := fun ⟨i, _⟩ ⟨j, _⟩ => M i j
  isSymm := by ext ⟨i, _⟩ ⟨j, _⟩; simp [Matrix.transpose, M.symmetric]
  diagonal := by intro ⟨i, _⟩; simp
  off_diagonal := by
    intro ⟨i, _⟩ ⟨j, _⟩ h
    exact M.off_diagonal _ _ (fun heq => h (Subtype.ext heq))

/-- Extend a vector $v : I \to \mathbb R$ to all of $B \to \mathbb R$ by setting components outside $I$ to zero. -/
noncomputable def extendByZero (I : Finset B) (v : ↥I → ℝ) : B → ℝ :=
  fun b => if h : b ∈ I then v ⟨b, h⟩ else 0

end CoxeterGroup
