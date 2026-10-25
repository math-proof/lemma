/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter5/Discrepancy.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
set_option maxHeartbeats 400000

open Finset BigOperators Real


noncomputable section

namespace Discrepancy

/-- Convert a `Bool` to a $\pm 1$ sign: `true ↦ 1`, `false ↦ -1`. -/
def boolSign (b : Bool) : ℤ := if b then 1 else -1

/-- The signed discrepancy of a $\pm 1$ coloring `f` on a set `S`:
$\operatorname{disc}(f, S) = \sum_{i \in S} \operatorname{sign}(f(i))$. -/
def disc {n : ℕ} (f : Fin n → Bool) (S : Finset (Fin n)) : ℤ :=
  ∑ i ∈ S, boolSign (f i)

end Discrepancy
end
