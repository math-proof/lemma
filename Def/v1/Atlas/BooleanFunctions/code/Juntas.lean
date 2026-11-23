/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/Juntas.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Def.v1.Atlas.BooleanFunctions.code.Influence
public import Theorem.Bool.Atlas.v1.BooleanFunctions.code.Influence
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

@[expose] public section

namespace BooleanFourier

noncomputable def highInfluenceCoords {n : ℕ} (f : (Fin n → Bool) → Bool) (τ : ℝ) :
    Finset (Fin n) :=
  Finset.univ.filter fun i => τ ≤ influence f i

end BooleanFourier
