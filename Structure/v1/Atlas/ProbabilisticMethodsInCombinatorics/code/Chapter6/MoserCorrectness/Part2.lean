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
import Def.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter6.MoserCorrectness
set_option maxHeartbeats 400000

open Finset


namespace MoserCorrectness

/-- A $k$-CNF formula over $n$ variables consisting of $m$ clauses, each of width exactly $k$. -/
structure KCNF (n m k : ℕ) where
  clauses : Fin m → Clause n k

end MoserCorrectness
