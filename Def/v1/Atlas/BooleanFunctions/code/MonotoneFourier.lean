/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/MonotoneFourier.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Def.v1.Atlas.BooleanFunctions.code.FourierExpansion
public import Theorem.Bool.Atlas.v1.BooleanFunctions.code.FourierExpansion
public import Theorem.Bool.Atlas.v1.BooleanFunctions.code.Influence
public import Theorem.Bool.Atlas.v1.BooleanFunctions.code.Monotone
public import Def.v1.Atlas.BooleanFunctions.code.Influence
public import Def.v1.Atlas.BooleanFunctions.code.Monotone
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith

@[expose] public section

open Finset BigOperators


namespace BooleanFourier

noncomputable def liftPM {n : ℕ} (f : (Fin n → Bool) → Bool) : (Fin n → Bool) → ℝ :=
  fun x => boolToReal (f x)

end BooleanFourier
