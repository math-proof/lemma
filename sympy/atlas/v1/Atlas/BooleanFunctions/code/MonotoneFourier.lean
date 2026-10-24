/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/MonotoneFourier.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.BooleanFunctions.code.FourierExpansion
import Lemma.Bool.Atlas.v1.BooleanFunctions.code.FourierExpansion
import Lemma.Bool.Atlas.v1.BooleanFunctions.code.Influence
import Lemma.Bool.Atlas.v1.BooleanFunctions.code.Monotone
import sympy.atlas.v1.Atlas.BooleanFunctions.code.Influence
import sympy.atlas.v1.Atlas.BooleanFunctions.code.Monotone
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

open Finset BigOperators

namespace BooleanFourier

noncomputable def liftPM {n : ℕ} (f : (Fin n → Bool) → Bool) : (Fin n → Bool) → ℝ :=
  fun x => boolToReal (f x)
