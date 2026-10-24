/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/InfluenceDerivative.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.BooleanFunctions.code.Influence
import Lemma.Bool.Atlas.v1.BooleanFunctions.code.Influence
import sympy.atlas.v1.Atlas.BooleanFunctions.code.Derivatives
import Mathlib.Tactic

namespace BooleanFourier

def boolToSign (b : Bool) : ℝ := if b then 1 else -1

noncomputable def boolDiscreteDerivative {n : ℕ} (g : (Fin (n + 1) → Bool) → ℝ)
    (i : Fin (n + 1)) : (Fin n → Bool) → ℝ :=
  fun y => (1 / 2 : ℝ) * (g (Fin.insertNth i true y) - g (Fin.insertNth i false y))
