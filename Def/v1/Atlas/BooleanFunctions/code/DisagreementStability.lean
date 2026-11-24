module
public import Def.v1.Atlas.BooleanFunctions.code.NoiseSensitivity
public import Theorem.Bool.Atlas.v1.BooleanFunctions.code.NoiseSensitivity
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp
open Finset BigOperators


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/DisagreementStability.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace BooleanFourier

noncomputable def disagreementProb {n : ℕ} (ρ : ℝ) (f : (Fin n → Bool) → ℝ) : ℝ :=
  (1 / (2 : ℝ) ^ n) * ∑ x : Fin n → Bool, (1 - f x * noiseOperator ρ f x) / 2

noncomputable def noiseSensitivityReal {n : ℕ} (δ : ℝ) (f : (Fin n → Bool) → ℝ) : ℝ :=
  disagreementProb (1 - 2 * δ) f

end BooleanFourier
