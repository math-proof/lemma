/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/Parseval.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Def.v1.Atlas.BooleanFunctions.code.FourierExpansion
public import Theorem.Bool.Atlas.v1.BooleanFunctions.code.FourierExpansion

@[expose] public section

open Finset BigOperators


namespace BooleanFourier

noncomputable def innerProduct {n : ℕ} (f g : (Fin n → Bool) → ℝ) : ℝ :=
  (1 / (2 : ℝ) ^ n) * ∑ x : Fin n → Bool, f x * g x

end BooleanFourier
