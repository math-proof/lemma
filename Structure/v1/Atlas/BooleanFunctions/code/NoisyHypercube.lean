/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/NoisyHypercube.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.BooleanFunctions.code.FourierExpansion
import Lemma.Bool.Atlas.v1.BooleanFunctions.code.FourierExpansion
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Def.v1.Atlas.BooleanFunctions.code.NoisyHypercube
open Finset BigOperators


namespace BooleanFourier

structure NoisyHypercube where
  n : ℕ
  ρ : ℝ
  hρ_nonneg : 0 ≤ ρ
  hρ_le_one : ρ ≤ 1

end BooleanFourier
