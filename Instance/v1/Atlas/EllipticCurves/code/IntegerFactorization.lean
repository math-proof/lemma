/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/IntegerFactorization.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.v1.Atlas.EllipticCurves.code.IntegerFactorization
open Nat Real Filter Asymptotics Finset


noncomputable section

/-- `B`-smoothness is decidable: it reduces to deciding membership of `n` in the
finite-indexed set `Nat.smoothNumbers (B + 1)`. -/
instance (B n : ℕ) : Decidable (IsSmooth B n) :=
  inferInstanceAs (Decidable (n ∈ Nat.smoothNumbers (B + 1)))

end
