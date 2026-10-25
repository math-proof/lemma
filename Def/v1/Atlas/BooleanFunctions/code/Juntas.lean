/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/Juntas.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.BooleanFunctions.code.Influence
import Lemma.Bool.Atlas.v1.BooleanFunctions.code.Influence
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Order.BigOperators.Group.Finset


namespace BooleanFourier

noncomputable def highInfluenceCoords {n : ℕ} (f : (Fin n → Bool) → Bool) (τ : ℝ) :
    Finset (Fin n) :=
  Finset.univ.filter fun i => τ ≤ influence f i

end BooleanFourier
