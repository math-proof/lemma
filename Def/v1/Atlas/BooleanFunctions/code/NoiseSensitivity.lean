module
public import Def.v1.Atlas.BooleanFunctions.code.Stability
public import Theorem.Bool.Atlas.v1.BooleanFunctions.code.Stability
public import Theorem.Bool.Atlas.v1.BooleanFunctions.code.Parseval
public import Def.v1.Atlas.BooleanFunctions.code.Parseval
open Finset BigOperators


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/NoiseSensitivity.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace BooleanFourier

noncomputable def noiseSensitivity {n : ℕ} (δ : ℝ) (f : (Fin n → Bool) → Bool) : ℝ :=
  (1 - noiseStability (1 - 2 * δ) (fun x => boolToReal (f x))) / 2

end BooleanFourier
