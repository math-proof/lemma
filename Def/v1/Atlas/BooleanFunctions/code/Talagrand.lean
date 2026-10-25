/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/Talagrand.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.BooleanFunctions.code.FourierExpansion
import Lemma.Bool.Atlas.v1.BooleanFunctions.code.FourierExpansion
import Def.v1.Atlas.BooleanFunctions.code.Definitions
import Theorem.v1.Atlas.BooleanFunctions.code.UncoveredBatch2
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
open Finset BigOperators


namespace BooleanFourier

noncomputable def expect {n : ℕ} (f : BoolFn n) : ℝ :=
  (1 / (2 : ℝ) ^ n) * ∑ x : Fin n → Bool, f x

noncomputable def variance {n : ℕ} (f : BoolFn n) : ℝ :=
  expect (fun x => f x ^ 2) - (expect f) ^ 2

noncomputable def fourierInfluence {n : ℕ} (f : BoolFn n) (i : Fin n) : ℝ :=
  ∑ S : Finset (Fin n), if i ∈ S then fourierCoeff f S ^ 2 else 0

end BooleanFourier
