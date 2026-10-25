/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter6/MoserCorrectness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic
import Structure.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter6.MoserCorrectness
set_option maxHeartbeats 400000

open Finset


namespace MoserCorrectness

/-- A Boolean assignment to $n$ variables. -/
abbrev Assignment (n : ℕ) := Fin n → Bool

end MoserCorrectness
