/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter9/HarperIsoperimetric.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
set_option maxHeartbeats 800000

open Finset


namespace HarperIsoperimetric

/-- The Hamming cube $\{0,1\}^n$, modeled as functions `Fin n → Bool`. -/
abbrev HammingCube (n : ℕ) := Fin n → Bool

end HarperIsoperimetric
