/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/DisagreementStability.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.BooleanFunctions.code.NoiseSensitivity
import Lemma.Bool.Atlas.v1.BooleanFunctions.code.NoiseSensitivity
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

open Finset BigOperators

namespace BooleanFourier

noncomputable def disagreementProb {n : ℕ} (ρ : ℝ) (f : (Fin n → Bool) → ℝ) : ℝ :=
  (1 / (2 : ℝ) ^ n) * ∑ x : Fin n → Bool, (1 - f x * noiseOperator ρ f x) / 2

noncomputable def noiseSensitivityReal {n : ℕ} (δ : ℝ) (f : (Fin n → Bool) → ℝ) : ℝ :=
  disagreementProb (1 - 2 * δ) f
