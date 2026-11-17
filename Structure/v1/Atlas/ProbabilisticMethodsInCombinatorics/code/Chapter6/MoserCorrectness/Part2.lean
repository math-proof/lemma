/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter6/MoserCorrectness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Finset.Basic
public import Mathlib.Tactic
public import Def.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter6.MoserCorrectness
public section

set_option maxHeartbeats 400000

open Finset


namespace MoserCorrectness

/-- A $k$-CNF formula over $n$ variables consisting of $m$ clauses, each of width exactly $k$. -/
structure KCNF (n m k : ℕ) where
  clauses : Fin m → Clause n k

end MoserCorrectness
