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
public import Def.v1.Atlas.TheoryOfComputation.code.NPCompleteness.Part8
public import Def.v1.Atlas.TheoryOfComputation.code.Clique

namespace ThreeSATToClique

/-- The polarity of a propositional literal: positive (`x`) or negative (`¬x`). -/
public inductive Polarity where
  | pos : Polarity
  | neg : Polarity
  deriving DecidableEq, Repr

end ThreeSATToClique
