/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/PCP.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Log
import Abbrev.v1.Atlas.BooleanFunctions.code.PCP


namespace PCP

def Language := ∀ (n : ℕ), Set (BinaryString n)

def IsPolynomial (f : ℕ → ℕ) : Prop :=
  ∃ (c k : ℕ), ∀ n, f n ≤ c * n ^ k + c

end PCP
