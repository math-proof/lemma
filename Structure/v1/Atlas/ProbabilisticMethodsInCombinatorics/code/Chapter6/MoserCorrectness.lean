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
set_option maxHeartbeats 400000

open Finset


namespace MoserCorrectness

/-- A propositional literal over $n$ variables: a variable index in $\text{Fin}\ n$ together with a Boolean polarity (`true` = positive, `false` = negated). -/
structure Literal (n : ℕ) where
  var : Fin n
  polarity : Bool

/-- A $k$-clause over $n$ variables: an indexed family of $k$ literals (interpreted as their disjunction). -/
structure Clause (n k : ℕ) where
  lits : Fin k → Literal n

end MoserCorrectness
