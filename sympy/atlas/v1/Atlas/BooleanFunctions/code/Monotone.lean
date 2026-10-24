/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/Monotone.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Order.Monotone.Basic
import Mathlib.Data.Bool.Basic
import Mathlib.Tactic
import sympy.atlas.v1.Atlas.BooleanFunctions.code.FourierExpansion
import Lemma.Bool.Atlas.v1.BooleanFunctions.code.FourierExpansion
import Lemma.Bool.Atlas.v1.BooleanFunctions.code.Influence
import sympy.atlas.v1.Atlas.BooleanFunctions.code.Influence

namespace BooleanFourier

def IsMonotone {n : ℕ} (f : (Fin n → Bool) → Bool) : Prop :=
  Monotone f
