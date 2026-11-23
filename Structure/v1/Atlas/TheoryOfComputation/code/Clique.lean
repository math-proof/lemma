/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/Clique.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Finset.Basic
public import Def.v1.Atlas.TheoryOfComputation.code.Complexity.Part2
public import Theorem.Nat.Atlas.v1.TheoryOfComputation.code.Complexity
public import Theorem.Nat.Atlas.v1.TheoryOfComputation.code.NPCompleteness
public import Def.v1.Atlas.TheoryOfComputation.code.NPCompleteness.Part8
public import Inductive.v1.Atlas.TheoryOfComputation.code.Clique


public section

namespace ThreeSATToClique

/-- A propositional literal: a variable index together with a polarity, so
that `⟨i, .pos⟩` represents `x_i` and `⟨i, .neg⟩` represents `¬x_i`. -/
structure Literal where
  varIdx : ℕ
  pol : Polarity
  deriving DecidableEq, Repr

end ThreeSATToClique
