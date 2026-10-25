/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter7/RandomGraphs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic
import Structure.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter7.RandomGraphs


noncomputable section

open Finset BigOperators

namespace RandomGraphs

/-- A configuration of $G(n, p)$: a Boolean assignment to each edge indicating
whether it is present. -/
abbrev Config (n : ℕ) := Edge n → Bool

end RandomGraphs
end
