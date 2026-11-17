/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/Derivatives.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Def.v1.Atlas.BooleanFunctions.code.Definitions
public import Mathlib.Data.Fin.Tuple.Basic

@[expose] public section

namespace BooleanFourier

noncomputable def discreteDerivative {n : ℕ} (f : BoolFn (n + 1))
    (i : Fin (n + 1)) : BoolFn n :=
  fun y => (1 / 2 : ℝ) * (f (Fin.insertNth i true y) - f (Fin.insertNth i false y))

end BooleanFourier
