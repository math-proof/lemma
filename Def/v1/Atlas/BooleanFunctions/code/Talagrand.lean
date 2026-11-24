module
public import Def.v1.Atlas.BooleanFunctions.code.FourierExpansion
public import Theorem.Bool.Atlas.v1.BooleanFunctions.code.FourierExpansion
public import Def.v1.Atlas.BooleanFunctions.code.Definitions
public import Theorem.v1.Atlas.BooleanFunctions.code.UncoveredBatch2
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith
open Finset BigOperators


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/Talagrand.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace BooleanFourier

noncomputable def expect {n : ℕ} (f : BoolFn n) : ℝ :=
  (1 / (2 : ℝ) ^ n) * ∑ x : Fin n → Bool, f x

noncomputable def variance {n : ℕ} (f : BoolFn n) : ℝ :=
  expect (fun x => f x ^ 2) - (expect f) ^ 2

noncomputable def fourierInfluence {n : ℕ} (f : BoolFn n) (i : Fin n) : ℝ :=
  ∑ S : Finset (Fin n), if i ∈ S then fourierCoeff f S ^ 2 else 0

end BooleanFourier
