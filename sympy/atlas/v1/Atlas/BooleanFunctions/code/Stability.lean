/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/Stability.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.BooleanFunctions.code.Hypercontractivity
import Lemma.Bool.Atlas.v1.BooleanFunctions.code.Hypercontractivity
import Lemma.Bool.Atlas.v1.BooleanFunctions.code.BonamilBeckner

import Mathlib.Data.Finset.SymmDiff
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Algebra.Order.Chebyshev

set_option maxHeartbeats 400000

set_option maxHeartbeats 1600000

open Finset BigOperators Real

namespace BooleanFourier

noncomputable def noiseOperator {n : ℕ} (ρ : ℝ) (f : (Fin n → Bool) → ℝ) :
    (Fin n → Bool) → ℝ :=
  fun x => ∑ y : Fin n → Bool,
    (∏ i : Fin n, ((1 + ρ * boolToReal (x i) * boolToReal (y i)) / 2)) * f y

noncomputable def noiseStability {n : ℕ} (ρ : ℝ) (f : (Fin n → Bool) → ℝ) : ℝ :=
  (1 / (2 : ℝ) ^ n) * ∑ x : Fin n → Bool, f x * noiseOperator ρ f x

noncomputable def majority (n : ℕ) (x : Fin n → Bool) : ℝ :=
  let numTrue := (Finset.univ.filter (fun i => x i = true)).card
  if numTrue * 2 > n then 1
  else if numTrue * 2 < n then -1
  else 0
