/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/NormalOrderCoeff.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic
import Abbrev.v1.Atlas.AlgebraicCombinatorics.code.NormalOrderCoeff
set_option autoImplicit false


noncomputable section

namespace NormalOrderCoeff

def pairsLE (ℓ : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range (ℓ + 1)) ×ˢ (Finset.range (ℓ + 1))).filter fun p => p.1 + p.2 ≤ ℓ

end NormalOrderCoeff
end
