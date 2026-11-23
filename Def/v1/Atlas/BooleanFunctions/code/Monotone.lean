/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/Monotone.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Order.Monotone.Basic
public import Mathlib.Data.Bool.Basic
public import Mathlib.Tactic
public import Def.v1.Atlas.BooleanFunctions.code.FourierExpansion
public import Theorem.Bool.Atlas.v1.BooleanFunctions.code.FourierExpansion
public import Theorem.Bool.Atlas.v1.BooleanFunctions.code.Influence
public import Def.v1.Atlas.BooleanFunctions.code.Influence

@[expose] public section

namespace BooleanFourier

def IsMonotone {n : ℕ} (f : (Fin n → Bool) → Bool) : Prop :=
  Monotone f

end BooleanFourier
