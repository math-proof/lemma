/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/Claim32Lec8.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.BooleanFunctions.code.EdgeExpansion
import Lemma.Bool.Atlas.v1.BooleanFunctions.code.EdgeExpansion
import Lemma.Bool.Atlas.v1.BooleanFunctions.code.Influence
import Def.v1.Atlas.BooleanFunctions.code.Influence
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.Ring


namespace BooleanAnalysis

open Finset

def indicator {n : ℕ} (A : Finset (Fin n → Bool)) : (Fin n → Bool) → Bool :=
  fun x => decide (x ∈ A)

end BooleanAnalysis
