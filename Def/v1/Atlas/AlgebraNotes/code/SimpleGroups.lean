/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraNotes/code/SimpleGroups.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib


namespace SimpleGroups

open Matrix

@[reducible] def lieAlgebraMatrix (n : ℕ) :
    LieAlgebra ℝ (Matrix (Fin n) (Fin n) ℝ) := inferInstance

noncomputable def lieAlgebraSet (m : ℕ) (G : Subgroup (GeneralLinearGroup (Fin m) ℝ)) :
    Set (Matrix (Fin m) (Fin m) ℝ) :=
  {A | ∀ t : ℝ, ∃ u : (Matrix (Fin m) (Fin m) ℝ)ˣ,
    (u : Matrix (Fin m) (Fin m) ℝ) = NormedSpace.exp (t • A) ∧ u ∈ G}

noncomputable def lieAlgebraSetPath (m : ℕ) (G : Subgroup (GeneralLinearGroup (Fin m) ℝ)) :
    Set (Matrix (Fin m) (Fin m) ℝ) :=
  {A | ∃ (ε : ℝ) (_ : ε > 0) (f : ℝ → Matrix (Fin m) (Fin m) ℝ),
    DifferentiableAt ℝ f 0 ∧
    f 0 = 1 ∧
    deriv f 0 = A ∧
    (∀ t : ℝ, |t| < ε → ∃ u : (Matrix (Fin m) (Fin m) ℝ)ˣ,
      (u : Matrix (Fin m) (Fin m) ℝ) = f t ∧ u ∈ G)}

open DualNumber in
noncomputable def lieAlgebraSetDual (m : ℕ)
    (P : Matrix (Fin m) (Fin m) ℝ[ε] → Prop) : Set (Matrix (Fin m) (Fin m) ℝ) :=
  {A | P ((1 : Matrix (Fin m) (Fin m) ℝ[ε]) + A.map (TrivSqZeroExt.inr))}


end SimpleGroups
