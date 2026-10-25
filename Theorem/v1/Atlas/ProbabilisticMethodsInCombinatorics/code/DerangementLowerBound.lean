/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/DerangementLowerBound.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Combinatorics.Derangements.Finite
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
set_option maxHeartbeats 400000

/-- Integer form of the derangement lower bound: for $n \ge 1$,
$D_n \cdot n^n \ge (n-1)^n \cdot n!$, where $D_n = $ `numDerangements n`. -/


namespace DerangementLowerBound

open Finset BigOperators Nat

end DerangementLowerBound
